From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Substitution.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Member access                                                                                    *)
(*                                                                                                *)
(* An object is of a class C with exact type arguments xs (invariant, owned or ref), and its member *)
(* variables have the declared types instantiated with those; it is of C itself, as only classes   *)
(* have member variables, and classes have no subtypes (BoundBaseType.Kind). A reference to it may *)
(* be of type C<ys>, with ys of any variance, as long as C<xs> is assignable to C<ys>. Through that *)
(* reference, BoundMemberVariableReadExpression and BoundObjectMemberAssignmentStatement            *)
(* instantiate the declared type of a member with ys instead. This shows that doing so is sound:  *)
(* - what is read is no more than what the reference says (member_read_sound): an in-variant type *)
(*   argument reads as `read Any?` (Subtyping.read_type);                                          *)
(* - what is written fits the member of the actual object (member_write_sound): a type parameter  *)
(*   bound to a variant type argument inside the type arguments of the member makes it take       *)
(*   nothing but Nothing (BoundTypeArgument.instantiateAllParametersForWriting); one as the type    *)
(*   of the member takes values for an in-variant type argument, but not for an out-variant one.   *)
(* For members whose declared type is a type parameter T of C, as it is, made nullable, of a given  *)
(* mutability or narrowed (`T?`, `mut T`, `T!`), or a class type of those, of any variance, and of  *)
(* class types of an explicit ownership (`Box<out T>`, `Map<K, Box<in mut V?>>?`), with types of   *)
(* the fragment of Transitivity.v; see member_type. The mutability of what is read,                *)
(* and the ownership of the members, is up to Ownership.v. A value written isn't of a non-nullable *)
(* Nothing, as there are no such values (the axiom that panic never returns): an out-variant type   *)
(* argument takes them, whatever their mutability. Likewise, a nullable Nothing holds nothing but   *)
(* null, which fits any nullable member.                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma uniform_fuel: forall {A: Type} (l: list A) (Q: nat -> A -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros A l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

Section MemberAccess.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

(* A type argument of an object: invariant, owned or ref, of a type of the fragment *)
Definition is_exact_argument (x: EType): bool :=
    match x with
    | TypeArgument Model.invariant o n =>
        match o with owned | ref => in_fragment env n | _ => false end
    | _ => false
    end.

(* A type parameter, as it is or nullable, of any mutability given to it or narrowed: `T`, `T?`,
   `mut T`, `T!` *)
Definition leaf_parameter (n: EType): option TypeParameterId :=
    match n with
    | Generic (mkGenericRef _ _ p _) => Some p
    | Nullable (Generic (mkGenericRef _ _ p _)) => Some p
    | _ => None
    end.

(* The ownership of a type argument that is the type parameter p: that of p, or an explicit one *)
Definition own_ownership (o: Ownership) (p: TypeParameterId): bool :=
    match o with parameter_ownership q => param_eqb q p | _ => true end.

(* A class type in the declared type of a member of class c: its type arguments are type parameters
   of c, as they are or nullable, of any variance; or class types such as this, of an explicit
   ownership *)
Fixpoint member_template (c: Class) (t: EType): bool :=
    match t with
    | RootResolved _ d arguments =>
        Nat.eqb (length arguments) (length (parameter_ids env d))
        && forallb (fun a =>
            match a with
            | TypeArgument _ o n =>
                match leaf_parameter n with
                | Some p => existsb (param_eqb p) (parameter_ids env c) && own_ownership o p
                | None => negb (is_parameter_ownership o) && member_template c n
                end
            | _ => false
            end) arguments
    | Nullable n => is_class n && member_template c n
    | _ => false
    end.

Definition member_argument (c: Class) (a: EType): bool :=
    match a with
    | TypeArgument _ o n =>
        match leaf_parameter n with
        | Some p => existsb (param_eqb p) (parameter_ids env c) && own_ownership o p
        | None => negb (is_parameter_ownership o) && member_template c n
        end
    | _ => false
    end.

(* The declared type of a member of class c *)
Definition member_type (c: Class) (f: EType): bool :=
    match leaf_parameter f with
    | Some p => existsb (param_eqb p) (parameter_ids env c)
    | None => member_template c f
    end.

(* The type read from a member, through a reference whose type arguments are the bindings: what
   unify takes the instantiated type for as an assignee (read_member_faithful) *)
Definition read_member (b: Bindings) (f: EType): EType :=
    match instantiate env b f with
    | TypeArgument v _ x => read_type v x
    | Nullable (TypeArgument v _ x) => rewrap_nullable (read_type v x)
    | t => t
    end.

(* The type written to a member, through a reference whose type arguments are the bindings
   (BoundTypeArgument.instantiateAllParametersForWriting) *)
Definition write_member (b: Bindings) (f: EType): EType :=
    if mentions_loosely_bound_in_arguments b f then
        match f with Nullable _ => Nullable bottom_type | _ => bottom_type end
    else instantiate env b f.

(* A type whose only value is null *)
Definition holds_only_null (V: EType): bool :=
    match V with Nullable n => is_non_nullable_nothing env n | _ => false end.

(* ---------------------------------------------------------------------------------------------- *)
(* The type arguments of the object and those of the reference                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma exact_argument_facts: forall x, is_exact_argument x = true ->
    exists o n, x = TypeArgument Model.invariant o n /\ in_fragment env n = true
        /\ argument_in_fragment env x = true /\ is_loose x = false.
Proof.
    intros [| | | |[] o n| |] H; simpl in H; try discriminate H.
    exists o, n. destruct o; try discriminate H. all: repeat split; first [reflexivity|exact H].
Qed.

(* The type arguments of a reference that an object is assignable to, pairwise *)
Lemma receiver_arguments: forall n s m c xs m' ys,
    c <> nothing -> length xs = length ys ->
    (forall x, In x xs -> argument_in_fragment env x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing s) = Some (Ongoing s) ->
    exists n', n = S n' /\ Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys.
Proof.
    intros [|n'] s m c xs m' ys Hc Hl Hxs Hys H; [discriminate H|]. exists n'. split; [reflexivity|].
    rewrite unify_classes in H.
    replace (base_type_is_subtype_of env c c) with true in H
        by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
    destruct (Model.is_subtype_of _ _); [|discriminate H].
    rewrite (class_eqb_false c nothing Hc), class_eqb_refl in H.
    apply (pairwise_of_arguments env n' ys xs s); [lia| |exact H].
    intros t a w Ht Ha E. apply (proj2 (keeps_states_with_arguments env wf n') t a s w); auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Members typed as a type parameter                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma member_parameter: forall c p,
    existsb (param_eqb p) (parameter_ids env c) = true -> exists i, nth_error (parameter_ids env c) i = Some p.
Proof.
    intros c p H. apply existsb_exists in H. destruct H as [q [Hq Hpq]]. apply param_eqb_eq in Hpq. subst q.
    apply In_nth_error. exact Hq.
Qed.

Lemma fragment_not_nesting: forall Y, in_fragment env Y = true -> nests_argument Y = false.
Proof. intros Y HY. destruct (fragment_cases env Y HY) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; reflexivity. Qed.

(* A reference to a type parameter bound to a type argument of type Y: the type argument, of the
   mutability and nullability of the reference applied to Y (GenericTypeReference.instantiateAllParameters,
   BoundTypeArgument.withMutability) *)
Lemma instantiate_bound_reference: forall b g v o Y,
    lookup_binding b (param_of g) = Some (TypeArgument v o Y) -> in_fragment env Y = true ->
    instantiate env b (Generic g) = final_argument (TypeArgument v o (inst_ref env g Y)).
Proof.
    intros b [gm nn p bp] v o Y H HY. cbn [param_of] in H.
    destruct (fragment_cases env Y HY) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        simpl; rewrite H; destruct v, o, gm, nn; reflexivity.
Qed.

(* A value assigned to a type argument *)
Lemma unify_argument_value: forall n v o t V s, in_fragment env V = true ->
    unify env (S n) (TypeArgument v o t) V (Ongoing s) =
    if Variance_beq v output then (if is_non_nullable_nothing env V then Some (Ongoing s) else Some Failed)
    else unify env n t V (Ongoing s).
Proof.
    intros n v o t V s HV. destruct (fragment_cases env V HV) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        destruct v; reflexivity.
Qed.

(* The type of the member, through the object and through the reference *)
Lemma parameter_member: forall n' s c xs ys p,
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    existsb (param_eqb p) (parameter_ids env c) = true ->
    exists o X v oy Y n'',
        lookup_binding (bindings_of env c xs) p = Some (TypeArgument Model.invariant o X)
        /\ lookup_binding (bindings_of env c ys) p = Some (TypeArgument v oy Y)
        /\ in_fragment env X = true /\ in_fragment env Y = true /\ n' = S n''
        /\ compare_variances (unify env n'') v Model.invariant Y X s = Some (Ongoing s).
Proof.
    intros n' s c xs ys p Hlx Hly Hxs Hys H Hp. destruct (member_parameter c p Hp) as [i Hi].
    destruct (nth_error_same_length _ xs i p (eq_sym Hlx) Hi) as [x Ex].
    destruct (nth_error_same_length _ ys i p (eq_sym Hly) Hi) as [y Ey].
    destruct (exact_argument_facts x (Hxs x (nth_error_In _ _ Ex))) as [o [X [-> [HX _]]]].
    pose proof (Hys y (nth_error_In _ _ Ey)) as Hy.
    destruct y as [| | | |v oy Y| |]; simpl in Hy; try discriminate Hy.
    pose proof (Forall2_nth_error _ xs ys i _ _ H Ex Ey) as E.
    destruct n' as [|n'']; [discriminate E|].
    rewrite unify_type_arguments in E by (apply (fragment_not_variable env); exact Hy).
    destruct (ownership_is_assignable_to o oy); [|discriminate E].
    exists o, X, v, oy, Y, n''. repeat split; auto.
    - exact (lookup_parameter env wf c xs i p _ Hi Ex).
    - exact (lookup_parameter env wf c ys i p _ Hi Ey).
Qed.

(* What a member of type T or T? reads as, of the mutability and nullability of the reference *)
Lemma read_member_reference: forall b g v o Y,
    lookup_binding b (param_of g) = Some (TypeArgument v o Y) -> in_fragment env Y = true ->
    read_member b (Generic g) = read_type v (inst_ref env g Y)
    /\ read_member b (Nullable (Generic g)) = rewrap_nullable (read_type v (inst_ref env g Y)).
Proof.
    intros b g v o Y H HY. unfold read_member.
    change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
    rewrite (instantiate_bound_reference b g v o Y H HY). pose proof (inst_ref_in_fragment env g Y HY) as HY'.
    set (Y' := inst_ref env g Y) in *. clearbody Y'.
    unfold final_argument. rewrite (fragment_not_nesting Y' HY'), orb_false_r.
    destruct (is_loose (TypeArgument v o Y')) eqn:El; [split; reflexivity|].
    assert (Hv: v = Model.invariant) by (destruct v; first [reflexivity|discriminate El]). subst v. cbn [read_type].
    destruct (fragment_cases env Y' HY') as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; split; reflexivity.
Qed.

(* How the type argument of an object, X, and that of a reference to it of variance v, Y, relate *)
Definition related (s: VariableStates) (v: Variance) (X Y: EType): Prop :=
    (v <> input -> exists f, unify env f Y X (Ongoing s) = Some (Ongoing s))
    /\ (v <> output -> exists f, unify env f X Y (Ongoing s) = Some (Ongoing s)).

Lemma related_of_compare: forall n s v X Y, in_fragment env X = true -> in_fragment env Y = true ->
    compare_variances (unify env n) v Model.invariant Y X s = Some (Ongoing s) -> related s v X Y.
Proof.
    intros n s v X Y HX HY H. destruct v; unfold compare_variances in H.
    - apply (both_ways (unify env n) Y X s) in H; [|apply unify_keeps_failure|].
      + split; intros _; exists n; apply H.
      + intros w. apply (proj1 (keeps_states_with_arguments env wf n)); assumption.
    - split; [intros C; exfalso; apply C; reflexivity|intros _; exists n; exact H].
    - split; [intros _; exists n; exact H|intros C; exfalso; apply C; reflexivity].
Qed.

Lemma compare_of_related: forall s v X Y, related s v X Y ->
    exists n, compare_variances (unify env n) v Model.invariant Y X s = Some (Ongoing s).
Proof.
    intros s v X Y [Hup Hdown]. destruct v; unfold compare_variances.
    - destruct (Hup ltac:(discriminate)) as [f1 H1]. destruct (Hdown ltac:(discriminate)) as [f2 H2].
      exists (f1 + f2). rewrite (unify_fuel_monotone env f1 (f1 + f2) _ _ _ _ ltac:(lia) H1).
      exact (unify_fuel_monotone env f2 (f1 + f2) _ _ _ _ ltac:(lia) H2).
    - exact (Hdown ltac:(discriminate)).
    - exact (Hup ltac:(discriminate)).
Qed.

Lemma exclusive_fits: forall m, Model.is_subtype_of exclusive m = true.
Proof. intros []; reflexivity. Qed.

(* A class type takes the mutability given and is assigned as it, or is of a const class *)
Lemma fit_cases: forall k x, in_fragment env x = true ->
    (assignment_mutability env (with_mutability env k x) = k /\ mutability_of env x = assignment_mutability env x)
    \/ (assignment_mutability env (with_mutability env k x) = exclusive /\ assignment_mutability env x = exclusive).
Proof.
    intros k x H. destruct (fragment_cases env x H) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        simpl; destruct (is_const (declaration_of env c)); first [right; split; reflexivity|left; split; reflexivity].
Qed.

Lemma inst_fit_mono: forall g X Y, in_fragment env X = true -> in_fragment env Y = true ->
    Model.is_subtype_of (assignment_mutability env X) (assignment_mutability env Y) = true ->
    Model.is_subtype_of (assignment_mutability env (inst_fit env g X)) (assignment_mutability env (inst_fit env g Y)) = true.
Proof.
    intros g X Y HX HY Hm. unfold inst_fit. destruct (given_mutability g) as [m|]; [|exact Hm].
    destruct (fit_cases (intersect_mutability (mutability_of env X) m) X HX) as [[EX MX]|[EX _]];
        rewrite EX; [|apply exclusive_fits].
    destruct (fit_cases (intersect_mutability (mutability_of env Y) m) Y HY) as [[EY MY]|[EY AY]]; rewrite EY.
    - rewrite MX, MY. apply intersect_mutability_greatest.
      + exact (mutability_subtype_trans _ _ _ (intersect_mutability_left _ _) Hm).
      + apply intersect_mutability_right.
    - rewrite AY in Hm. apply mutability_subtype_of_exclusive in Hm. rewrite MX, Hm. destruct m; reflexivity.
Qed.

(* Where Y is above X, the reference to a type parameter bound to Y is above the one bound to X *)
Lemma inst_ref_mono: forall g f X Y s, in_fragment env X = true -> in_fragment env Y = true ->
    unify env f Y X (Ongoing s) = Some (Ongoing s) ->
    unify env f (inst_ref env g Y) (inst_ref env g X) (Ongoing s) = Some (Ongoing s).
Proof.
    intros g f X Y s HX HY H.
    pose proof (accepted_mutability_classes env f Y X s s HY HX H) as Hm.
    assert (Hf: unify env f (inst_fit env g Y) (inst_fit env g X) (Ongoing s) = Some (Ongoing s)).
    { apply (unify_remut env f Y _ X _ s s (remut_inst_fit env g Y HY) (remut_inst_fit env g X HX)); [|exact H].
      apply inst_fit_mono; assumption. }
    unfold inst_ref. destruct (is_narrowed g); [|exact Hf].
    apply (unify_without_null env); [apply (inst_fit_in_fragment env); exact HY|apply (inst_fit_in_fragment env); exact HX|exact Hf].
Qed.

Lemma related_inst_ref: forall g s v X Y, in_fragment env X = true -> in_fragment env Y = true ->
    related s v X Y -> related s v (inst_ref env g X) (inst_ref env g Y).
Proof.
    intros g s v X Y HX HY [Hup Hdown]. split.
    - intros Hv. destruct (Hup Hv) as [f Hf]. exists f. apply inst_ref_mono; assumption.
    - intros Hv. destruct (Hdown Hv) as [f Hf]. exists f. apply inst_ref_mono; assumption.
Qed.

(* As the target, a type argument takes what its type, of the fragment, takes *)
Lemma final_argument_target: forall f v o Y V s, in_fragment env V = true -> in_fragment env Y = true ->
    unify env f (final_argument (TypeArgument v o Y)) V (Ongoing s) = Some (Ongoing s) ->
    exists f', unify env f' (TypeArgument v o Y) V (Ongoing s) = Some (Ongoing s).
Proof.
    intros f v o Y V s HV HY H. unfold final_argument in H. rewrite (fragment_not_nesting Y HY), orb_false_r in H.
    destruct (is_loose (TypeArgument v o Y)) eqn:El; [exists f; exact H|].
    assert (Hv: v = Model.invariant) by (destruct v; first [reflexivity|discriminate El]). subst v.
    exists (S f). rewrite (unify_argument_value f Model.invariant o Y V s HV). exact H.
Qed.

Lemma nullable_final_argument_target: forall f v o Y V s, in_fragment env V = true -> in_fragment env Y = true ->
    unify env f (rewrap_nullable (final_argument (TypeArgument v o Y))) V (Ongoing s) = Some (Ongoing s) ->
    exists f', unify env f' (rewrap_nullable (TypeArgument v o Y)) V (Ongoing s) = Some (Ongoing s).
Proof.
    intros f v o Y V s HV HY H. unfold final_argument in H. rewrite (fragment_not_nesting Y HY), orb_false_r in H.
    destruct (is_loose (TypeArgument v o Y)) eqn:El; [exists f; exact H|].
    assert (Hv: v = Model.invariant) by (destruct v; first [reflexivity|discriminate El]). subst v.
    destruct f as [|f]; [discriminate H|]. exists (S (S (S f))). cbn [rewrap_nullable].
    destruct (fragment_cases env Y HY) as [[my [cy [ay ->]]]|[my [cy [ay [-> HY0]]]]];
    destruct (fragment_cases env V HV) as [[mv [cv [av ->]]]|[mv [cv [av [-> HV0]]]]]; cbn [rewrap_nullable] in H.
    - rewrite unify_nullable_class in H |- *. rewrite (unify_argument_value _ Model.invariant o _ _ s HV).
      apply (unify_fuel_monotone env f); [lia|exact H].
    - rewrite unify_nullable_nullable in H |- *. rewrite (unify_argument_value _ Model.invariant o _ _ s HV0).
      apply (unify_fuel_monotone env f); [lia|exact H].
    - rewrite unify_nullable_class in H |- *. rewrite (unify_argument_value _ Model.invariant o _ _ s HV).
      rewrite unify_nullable_class. apply (unify_fuel_monotone env f); [lia|exact H].
    - rewrite unify_nullable_nullable in H |- *. rewrite (unify_argument_value _ Model.invariant o _ _ s HV0).
      rewrite unify_nullable_class. apply (unify_fuel_monotone env f); [lia|exact H].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Nullable types                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma rewrap_in_fragment: forall X, in_fragment env X = true -> in_fragment env (rewrap_nullable X) = true.
Proof.
    intros X HX. destruct (fragment_cases env X HX) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact HX.
Qed.

Lemma rewrap_is_nullable: forall t, is_nullable env (rewrap_nullable t) = true.
Proof. intros [| | | | | |]; reflexivity. Qed.

(* Where Y is above X, so is Y? above X? *)
Lemma rewrap_mono: forall f X Y s, in_fragment env X = true -> in_fragment env Y = true ->
    unify env f Y X (Ongoing s) = Some (Ongoing s) ->
    unify env (S f) (rewrap_nullable Y) (rewrap_nullable X) (Ongoing s) = Some (Ongoing s).
Proof.
    intros f X Y s HX HY H.
    destruct (fragment_cases env X HX) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> _]]]]];
        destruct (fragment_cases env Y HY) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> _]]]]]; cbn [rewrap_nullable].
    - rewrite unify_nullable_nullable. exact H.
    - rewrite unify_nullable_nullable. destruct f as [|f]; [discriminate H|]. rewrite unify_nullable_class in H.
      apply (unify_fuel_monotone env f); [lia|exact H].
    - destruct f as [|f]; [discriminate H|]. rewrite unify_class_nullable in H. discriminate H.
    - apply (unify_fuel_monotone env f); [lia|exact H].
Qed.

(* Where X is above V, so is X? *)
Lemma rewrap_above: forall f X V s, in_fragment env X = true -> in_fragment env V = true ->
    unify env f X V (Ongoing s) = Some (Ongoing s) ->
    unify env (S f) (rewrap_nullable X) V (Ongoing s) = Some (Ongoing s).
Proof.
    intros f X V s HX HV H.
    destruct (fragment_cases env X HX) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> _]]]]]; cbn [rewrap_nullable].
    - destruct (fragment_cases env V HV) as [[mv [cv [vargs ->]]]|[mv [cv [vargs [-> _]]]]].
      + rewrite unify_nullable_class. exact H.
      + destruct f as [|f]; [discriminate H|]. rewrite unify_class_nullable in H. discriminate H.
    - apply (unify_fuel_monotone env f); [lia|exact H].
Qed.

(* `exclusive Nothing` is assignable to every type of the fragment *)
Lemma bottom_below: forall t f s, in_fragment env t = true -> 2 <= f -> unify env f t bottom_type (Ongoing s) = Some (Ongoing s).
Proof.
    intros t f s Ht Hf. apply (below_bottom env wf 1 bottom_type s (bottom_in_fragment env wf)); [|exact Ht|exact Hf].
    apply (proj1 (reflexivity_with_arguments env 1)); [exact (bottom_in_fragment env wf)|simpl; lia].
Qed.

(* Every type of the fragment is assignable to `read Any?` *)
Lemma top_above: forall t f s, in_fragment env t = true -> 2 <= f -> unify env f top_type t (Ongoing s) = Some (Ongoing s).
Proof.
    intros t f s Ht Hf. apply (above_top env wf 2 top_type s (top_in_fragment env wf)); [|exact Ht|exact Hf].
    apply (proj1 (reflexivity_with_arguments env 2)); [exact (top_in_fragment env wf)|simpl; lia].
Qed.

(* Kotlin keeps the type argument a member of type T or T? is instantiated to, and unify reads it
   when it is assigned: as read_member has it *)
Lemma read_member_faithful: forall b f D fuel s, in_fragment env D = true ->
    unify env fuel D (instantiate env b f) (Ongoing s) = Some (Ongoing s) ->
    exists fuel', unify env fuel' D (read_member b f) (Ongoing s) = Some (Ongoing s).
Proof.
    intros b f D fuel s HD H. unfold read_member.
    destruct (instantiate env b f) as [| [| | | |v o x| |] | | |v o x| |]; try (exists fuel; exact H).
    - (* T? *)
      destruct fuel as [|fuel]; [discriminate H|].
      destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]];
          [rewrite unify_class_nullable in H; discriminate H|].
      rewrite unify_nullable_nullable in H. destruct fuel as [|fuel]; [discriminate H|].
      rewrite unify_step_once in H. unfold unify_step, unify_root_resolved in H.
      destruct (read_type v x) as [| | | | | |] eqn:Er; cbn [rewrap_nullable];
          try (exists (S (S fuel)); rewrite unify_nullable_nullable; apply (unify_fuel_monotone env fuel); [lia|exact H]).
      destruct fuel as [|fuel]; [discriminate H|]. rewrite unify_class_nullable in H. discriminate H.
    - (* T *)
      destruct fuel as [|fuel]; [discriminate H|]. exists fuel.
      destruct (fragment_cases env D HD) as [[md [cd [dargs ->]]]|[md [cd [dargs [-> _]]]]];
          rewrite unify_step_once in H; exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Members typed as a class type                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma member_root: forall c m d arguments, member_template c (RootResolved m d arguments) = true ->
    length arguments = length (parameter_ids env d) /\ forall a, In a arguments -> member_argument c a = true.
Proof.
    intros c m d arguments H.
    change (Nat.eqb (length arguments) (length (parameter_ids env d)) && forallb (member_argument c) arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hl Ha]. split; [apply Nat.eqb_eq, Hl|apply forallb_forall, Ha].
Qed.

Lemma member_cases: forall c t, member_template c t = true ->
    (exists m d arguments, t = RootResolved m d arguments) \/
    (exists m d arguments, t = Nullable (RootResolved m d arguments) /\ member_template c (RootResolved m d arguments) = true).
Proof.
    intros c [m d arguments|[m d arguments| | | | | |]| | | | |] H; simpl in H; try discriminate H.
    - left. eauto.
    - right. eauto.
Qed.

Lemma member_shape: forall c t, member_template c t = true -> class_shaped t.
Proof.
    intros c t H. destruct (member_cases c t H) as [[m [d [arguments ->]]]|[m [d [arguments [-> _]]]]]; [left|right]; eauto.
Qed.

Lemma member_instance_shape: forall c b t, member_template c t = true -> class_shaped (instantiate env b t).
Proof.
    intros c b t H. destruct (member_cases c t H) as [[m [d [arguments ->]]]|[m [d [arguments [-> _]]]]].
    - left. exists m, d, (map (instantiate env b) arguments). reflexivity.
    - right. exists m, d, (map (instantiate env b) arguments). reflexivity.
Qed.

Lemma member_argument_kind: forall c a, member_argument c a = true ->
    exists w o n, a = TypeArgument w o n /\
        ((exists p, leaf_parameter n = Some p /\ existsb (param_eqb p) (parameter_ids env c) = true /\ own_ownership o p = true)
         \/ (leaf_parameter n = None /\ is_parameter_ownership o = false /\ member_template c n = true)).
Proof.
    intros c [| | | |w o n| |] H; unfold member_argument in H; try discriminate H. exists w, o, n. split; [reflexivity|].
    destruct (leaf_parameter n) as [p|] eqn:E; apply andb_true_iff in H; destruct H as [H1 H2].
    - left. exists p. auto.
    - right. split; [reflexivity|]. split; [|exact H2]. destruct o; auto; discriminate H1.
Qed.

(* The type parameter of a leaf, as it is or nullable *)
Definition wrap_leaf (nullable: bool) (n: EType): EType := if nullable then Nullable n else n.

Lemma leaf_cases: forall n p, leaf_parameter n = Some p -> exists g nl, n = wrap_leaf nl (Generic g) /\ param_of g = p.
Proof.
    intros [|[| |[gm nn q bq]| | | |]|[gm nn q bq]| | | |] p H; simpl in H; try discriminate H; injection H as <-.
    - exists (mkGenericRef gm nn q bq), true. split; reflexivity.
    - exists (mkGenericRef gm nn q bq), false. split; reflexivity.
Qed.

Definition wrap (nullable: bool) (X: EType): EType := if nullable then rewrap_nullable X else X.

Lemma wrap_in_fragment: forall nl X, in_fragment env X = true -> in_fragment env (wrap nl X) = true.
Proof. intros [] X HX; [apply rewrap_in_fragment|]; exact HX. Qed.

Lemma wrap_mono: forall nl f X Y s, in_fragment env X = true -> in_fragment env Y = true ->
    unify env f Y X (Ongoing s) = Some (Ongoing s) ->
    unify env (S f) (wrap nl Y) (wrap nl X) (Ongoing s) = Some (Ongoing s).
Proof.
    intros [] f X Y s HX HY H; [apply rewrap_mono; assumption|]. apply (unify_fuel_monotone env f); [lia|exact H].
Qed.

(* `out T`, `in mut T?` and the like: the variances merge (see Subtyping.instantiate) *)
Lemma instantiate_leaf: forall b w o g nl v oa A,
    lookup_binding b (param_of g) = Some (TypeArgument v oa A) -> in_fragment env A = true ->
    instantiate env b (TypeArgument w o (wrap_leaf nl (Generic g))) =
    if Variance_beq v Model.invariant || Variance_beq w Model.invariant || Variance_beq v w
    then TypeArgument (if Variance_beq v Model.invariant then w else v) (instantiate_ownership b o) (wrap nl (inst_ref env g A))
    else match w with
         | output => TypeArgument output (instantiate_ownership b o) top_type
         | _ => TypeArgument input (instantiate_ownership b o) bottom_type
         end.
Proof.
    intros b w o [gm nn p bp] nl v oa A Hb HA. cbn [param_of] in Hb.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        destruct nl; simpl; rewrite Hb; destruct v, oa, w, gm, nn; reflexivity.
Qed.

Lemma ownership_refl: forall o, ownership_is_assignable_to o o = true.
Proof. intros [| | |q]; simpl; try rewrite param_eqb_refl; reflexivity. Qed.

(* The instances of a member type, through the object and through the reference: of the fragment;
   the one through the reference above the other; and below it, too, where the reference doesn't
   widen it *)
Definition compares (frag: EType -> bool) (s: VariableStates) (ix iy: EType) (widened: bool): Prop :=
    frag ix = true /\ frag iy = true
    /\ (exists f, unify env f iy ix (Ongoing s) = Some (Ongoing s))
    /\ (widened = false -> exists f, unify env f ix iy (Ongoing s) = Some (Ongoing s)).

(* `T`, `out T?` and the like, in a member type *)
Lemma leaf_member: forall n' s c xs ys w o n p,
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    leaf_parameter n = Some p -> existsb (param_eqb p) (parameter_ids env c) = true -> own_ownership o p = true ->
    compares (argument_in_fragment env) s
        (instantiate env (bindings_of env c xs) (TypeArgument w o n)) (instantiate env (bindings_of env c ys) (TypeArgument w o n))
        (mentions_loosely_bound (bindings_of env c ys) (TypeArgument w o n))
    /\ mentions_loosely_bound (bindings_of env c xs) (TypeArgument w o n) = false.
Proof.
    intros n' s c xs ys w o n p Hlx Hly Hxs Hys H Hn Hp Ho.
    destruct (leaf_cases n p Hn) as [g [nl [-> <-]]].
    destruct (member_parameter c (param_of g) Hp) as [i Hi].
    destruct (nth_error_same_length _ xs i _ (eq_sym Hlx) Hi) as [x Ex].
    destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
    pose proof (Hxs x (nth_error_In _ _ Ex)) as Hex.
    destruct (exact_argument_facts x Hex) as [ox [X [-> [HX [_ _]]]]].
    assert (Hox: ox = owned \/ ox = ref) by (simpl in Hex; destruct ox; auto; discriminate Hex).
    pose proof (Hys y (nth_error_In _ _ Ey)) as Hy.
    destruct y as [| | | |vy oy Y| |]; simpl in Hy; try discriminate Hy.
    pose proof (Forall2_nth_error _ xs ys i _ _ H Ex Ey) as E.
    destruct n' as [|n'']; [discriminate E|].
    rewrite unify_type_arguments in E by (apply (fragment_not_variable env); exact Hy).
    destruct (ownership_is_assignable_to ox oy) eqn:Eo; [|discriminate E].
    pose proof (lookup_parameter env wf c xs i (param_of g) _ Hi Ex) as Lx.
    pose proof (lookup_parameter env wf c ys i (param_of g) _ Hi Ey) as Ly.
    assert (Hm: forall b a, lookup_binding b (param_of g) = Some a ->
        mentions_loosely_bound b (TypeArgument w o (wrap_leaf nl (Generic g))) = is_loose a).
    { intros b a Hb. destruct g as [gm nn q bq]. destruct nl; simpl in Hb |- *; rewrite Hb; reflexivity. }
    rewrite (Hm _ _ Lx), (Hm _ _ Ly).
    rewrite (instantiate_leaf _ w o g nl _ _ _ Lx HX), (instantiate_leaf _ w o g nl _ _ _ Ly Hy).
    split; [|simpl; destruct Hox as [-> | ->]; reflexivity].
    (* the ownerships *)
    assert (Hown: ownership_is_assignable_to (instantiate_ownership (bindings_of env c xs) o)
        (instantiate_ownership (bindings_of env c ys) o) = true).
    { destruct o as [| | |q]; try reflexivity. simpl in Ho. apply param_eqb_eq in Ho. subst q. simpl. rewrite Lx, Ly. exact Eo. }
    assert (Hown2: is_loose (TypeArgument vy oy Y) = false -> ownership_is_assignable_to
        (instantiate_ownership (bindings_of env c ys) o) (instantiate_ownership (bindings_of env c xs) o) = true).
    { intros Hl. assert (oy = ox).
      { simpl in Hl. apply orb_false_iff in Hl. destruct Hl as [_ Hl].
        destruct Hox as [-> | ->]; destruct oy; simpl in Eo, Hl; congruence. }
      subst oy. destruct o as [| | |q]; try reflexivity. simpl in Ho. apply param_eqb_eq in Ho. subst q. simpl.
      rewrite Lx, Ly. apply ownership_refl. }
    (* the instances of the reference to the type parameter, of its mutability and nullability *)
    pose proof (inst_ref_in_fragment env g X HX) as HX'. pose proof (inst_ref_in_fragment env g Y Hy) as HY'.
    destruct (compare_of_related s vy _ _ (related_inst_ref g s vy X Y HX Hy (related_of_compare n'' s vy X Y HX Hy E)))
        as [n3 E3].
    change (is_loose (TypeArgument vy oy Y)) with (is_loose (TypeArgument vy oy (inst_ref env g Y))) in Hown2 |- *.
    set (X' := inst_ref env g X) in *. set (Y' := inst_ref env g Y) in *. clearbody X' Y'.
    clear E Hex Ex Ey Lx Ly Hm HX Hy H n''. clear X Y.
    rename X' into X, Y' into Y, HX' into HX, HY' into Hy, E3 into E, n3 into n''.
    set (wX := wrap nl X). set (wY := wrap nl Y).
    assert (HwX: in_fragment env wX = true) by (apply wrap_in_fragment; exact HX).
    assert (HwY: in_fragment env wY = true) by (apply wrap_in_fragment; exact Hy).
    assert (Hwm: forall A B, in_fragment env A = true -> in_fragment env B = true -> unify env n'' B A (Ongoing s) = Some (Ongoing s) ->
        unify env (S n'' + 2) (wrap nl B) (wrap nl A) (Ongoing s) = Some (Ongoing s)).
    { intros A B HA HB E0. apply (unify_fuel_monotone env (S n'')); [lia|]. apply wrap_mono; assumption. }
    assert (Ftop: unify env (S n'' + 2) top_type wX (Ongoing s) = Some (Ongoing s)) by (apply top_above; [exact HwX|lia]).
    assert (Fbot: unify env (S n'' + 2) wX bottom_type (Ongoing s) = Some (Ongoing s)) by (apply bottom_below; [exact HwX|lia]).
    set (ox' := instantiate_ownership (bindings_of env c xs) o) in *.
    set (oy' := instantiate_ownership (bindings_of env c ys) o) in *.
    set (F := S n'' + 2) in *.
    destruct vy; cbn [compare_variances] in E.
    - (* an invariant type argument *)
      apply (both_ways (unify env n'') Y X s) in E;
          [|apply unify_keeps_failure|intros w0; apply (proj1 (keeps_states_with_arguments env wf n'')); assumption].
      destruct E as [E1 E2].
      pose proof (Hwm X Y HX Hy E1) as FYX. pose proof (Hwm Y X Hy HX E2) as FXY. fold wX wY in FYX, FXY.
      clearbody wX wY ox' oy' F.
      destruct w; cbn [Variance_beq orb]; unfold compares;
          (split; [exact HwX|]); (split; [first [exact HwY|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)]|]);
          (split; [exists (S F); rewrite unify_type_arguments by (first [reflexivity|apply (fragment_not_variable env); assumption]);
                   rewrite Hown; cbn [compare_variances]; first [exact FYX|exact FXY|rewrite FYX; exact FXY]|]);
          intros Hl; exists (S F); rewrite unify_type_arguments by (first [reflexivity|apply (fragment_not_variable env); assumption]);
          rewrite (Hown2 Hl); cbn [compare_variances]; first [rewrite FXY; exact FYX|exact FXY|exact FYX].
    - (* an in-variant type argument *)
      pose proof (Hwm Y X Hy HX E) as FXY. fold wX wY in FXY.
      clearbody wX wY ox' oy' F.
      destruct w; cbn [Variance_beq orb]; unfold compares;
          (split; [exact HwX|]); (split; [first [exact HwY|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)]|]);
          (split; [exists (S F); rewrite unify_type_arguments by (first [reflexivity|apply (fragment_not_variable env); assumption]);
                   rewrite Hown; cbn [compare_variances]; first [exact FXY|exact Ftop|exact Fbot]|]);
          intros Hl; discriminate Hl.
    - (* an out-variant type argument *)
      pose proof (Hwm X Y HX Hy E) as FYX. fold wX wY in FYX.
      clearbody wX wY ox' oy' F.
      destruct w; cbn [Variance_beq orb]; unfold compares;
          (split; [exact HwX|]); (split; [first [exact HwY|exact (top_in_fragment env wf)|exact (bottom_in_fragment env wf)]|]);
          (split; [exists (S F); rewrite unify_type_arguments by (first [reflexivity|apply (fragment_not_variable env); assumption]);
                   rewrite Hown; cbn [compare_variances]; first [exact FYX|exact Ftop|exact Fbot]|]);
          intros Hl; discriminate Hl.
Qed.

Lemma fold_pairs: forall n (targs aargs: list EType) s,
    Forall2 (fun a t => unify env n t a (Ongoing s) = Some (Ongoing s)) aargs targs ->
    unify_arguments (unify env n) targs aargs s = Some (Ongoing s).
Proof.
    intros n targs aargs s H. unfold unify_arguments. revert targs H.
    induction aargs as [|a aargs IH]; intros targs H; inversion H; subst; [reflexivity|].
    simpl. match goal with E: unify env n ?t a _ = _ |- _ => rewrite E end. apply IH. assumption.
Qed.

(* The instances of member types, through the object and through the reference *)
Lemma member_instances: forall n' s c xs ys,
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    forall k,
    (forall t, depth t <= k -> member_template c t = true ->
        compares (in_fragment env) s (instantiate env (bindings_of env c xs) t) (instantiate env (bindings_of env c ys) t)
            (mentions_loosely_bound (bindings_of env c ys) t)
        /\ mentions_loosely_bound (bindings_of env c xs) t = false)
    /\ (forall a, argument_depth a <= k -> member_argument c a = true ->
        compares (argument_in_fragment env) s (instantiate env (bindings_of env c xs) a) (instantiate env (bindings_of env c ys) a)
            (mentions_loosely_bound (bindings_of env c ys) a)
        /\ mentions_loosely_bound (bindings_of env c xs) a = false).
Proof.
    intros n' s c xs ys Hlx Hly Hxs Hys H k.
    set (bX := bindings_of env c xs). set (bY := bindings_of env c ys).
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht. destruct (member_cases c t Ht) as [[m [d [args ->]]]|[m [d [args [-> _]]]]]; simpl in Hd; lia.
      - intros a Hd Ha. destruct (member_argument_kind c a Ha) as [w [o [n [-> _]]]]. simpl in Hd. lia. }
    assert (Hroot: forall m d args, depth (RootResolved m d args) <= S k -> member_template c (RootResolved m d args) = true ->
        compares (in_fragment env) s (RootResolved m d (map (instantiate env bX) args)) (RootResolved m d (map (instantiate env bY) args))
            (existsb (mentions_loosely_bound bY) args)
        /\ existsb (mentions_loosely_bound bX) args = false).
    { intros m d args Hd Ht. destruct (member_root c m d args Ht) as [Hl Hargs].
      assert (IH: forall a, In a args ->
          compares (argument_in_fragment env) s (instantiate env bX a) (instantiate env bY a) (mentions_loosely_bound bY a)
          /\ mentions_loosely_bound bX a = false).
      { intros a Ha. apply IHa; [pose proof (argument_depth_below m d args a Ha); lia|exact (Hargs a Ha)]. }
      assert (Hfrag: forall b, (forall a, In a args -> argument_in_fragment env (instantiate env b a) = true) ->
          in_fragment env (RootResolved m d (map (instantiate env b) args)) = true).
      { intros b Hb. change (Nat.eqb (length (map (instantiate env b) args)) (length (parameter_ids env d))
            && forallb (argument_in_fragment env) (map (instantiate env b) args) = true).
        rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
        destruct Ha' as [a [<- Ha]]. exact (Hb a Ha). }
      assert (Hsame: forall F Ay Ax, Forall2 (fun a t => unify env F t a (Ongoing s) = Some (Ongoing s)) Ax Ay ->
          unify env (S F) (RootResolved m d Ay) (RootResolved m d Ax) (Ongoing s) = Some (Ongoing s)).
      { intros F Ay Ax HA. rewrite unify_classes. replace (base_type_is_subtype_of env d d) with true
            by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
        rewrite (assignment_mutability_of_class env m d Ax Ay), mutability_is_subtype_of_refl.
        destruct (class_eqb d nothing); [reflexivity|]. rewrite class_eqb_refl. apply fold_pairs. exact HA. }
      split; [|apply not_true_iff_false; intros E; apply existsb_exists in E; destruct E as [a [Ha E]];
               rewrite (proj2 (IH a Ha)) in E; discriminate E].
      unfold compares. split; [apply Hfrag; intros a Ha; exact (proj1 (proj1 (IH a Ha)))|].
      split; [apply Hfrag; intros a Ha; exact (proj1 (proj2 (proj1 (IH a Ha))))|].
      split.
      - destruct (uniform_fuel args (fun f a => unify env f (instantiate env bY a) (instantiate env bX a) (Ongoing s) = Some (Ongoing s)))
            as [F HF].
        { intros f f' a Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
        { intros a Ha. exact (proj1 (proj2 (proj2 (proj1 (IH a Ha))))). }
        exists (S F). apply Hsame. apply Forall2_map_same. exact HF.
      - intros Hm. pose proof (mentions_arguments_false _ args Hm) as Hma.
        destruct (uniform_fuel args (fun f a => unify env f (instantiate env bX a) (instantiate env bY a) (Ongoing s) = Some (Ongoing s)))
            as [F HF].
        { intros f f' a Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
        { intros a Ha. exact (proj2 (proj2 (proj2 (proj1 (IH a Ha)))) (Hma a Ha)). }
        exists (S F). apply Hsame. apply Forall2_map_same. exact HF. }
    split.
    - intros t Hd Ht. destruct (member_cases c t Ht) as [[m [d [args ->]]]|[m [d [args [-> Ht']]]]].
      + exact (Hroot m d args Hd Ht).
      + rewrite depth_nullable in Hd. destruct (Hroot m d args ltac:(lia) Ht') as [[Hfx [Hfy [[f Hf] Hb]]] Hmx].
        split; [|exact Hmx]. unfold compares.
        change (instantiate env bX (Nullable (RootResolved m d args))) with (Nullable (RootResolved m d (map (instantiate env bX) args))).
        change (instantiate env bY (Nullable (RootResolved m d args))) with (Nullable (RootResolved m d (map (instantiate env bY) args))).
        change (mentions_loosely_bound bY (Nullable (RootResolved m d args))) with (existsb (mentions_loosely_bound bY) args).
        split; [exact Hfx|]. split; [exact Hfy|]. split.
        * exists (S f). rewrite unify_nullable_nullable. exact Hf.
        * intros Hm. destruct (Hb Hm) as [g Hg]. exists (S g). rewrite unify_nullable_nullable. exact Hg.
    - intros a Hd Ha. destruct (member_argument_kind c a Ha) as [w [o [n [-> [[p [Hn [Hp Ho]]]|[Hn [Ho Hnt]]]]]]].
      + exact (leaf_member n' s c xs ys w o n p Hlx Hly Hxs Hys H Hn Hp Ho).
      + simpl in Hd. destruct (IHt n ltac:(lia) Hnt) as [[Hfx [Hfy [[f Hf] Hb]]] Hmx].
        pose proof (member_shape c n Hnt) as Hshape.
        change (mentions_loosely_bound bY (TypeArgument w o n)) with (mentions_loosely_bound bY n).
        change (mentions_loosely_bound bX (TypeArgument w o n)) with (mentions_loosely_bound bX n).
        rewrite (instantiate_template_argument env bX w o n Ho Hshape), (instantiate_template_argument env bY w o n Ho Hshape), Hmx.
        split; [|reflexivity]. unfold compares.
        set (ix := instantiate env bX n) in *. set (iy := instantiate env bY n) in *.
        destruct (mentions_loosely_bound bY n) eqn:Em.
        * (* widened through the reference *)
          assert (Fbot: unify env (f + 2) ix bottom_type (Ongoing s) = Some (Ongoing s)) by (apply bottom_below; [exact Hfx|lia]).
          assert (Ff: unify env (f + 2) iy ix (Ongoing s) = Some (Ongoing s)) by (apply (unify_fuel_monotone env f); [lia|exact Hf]).
          clearbody ix iy.
          destruct w; cbn iota; (split; [exact Hfx|]);
              (split; [first [exact Hfy|exact (bottom_in_fragment env wf)]|]);
              (split; [|intros E; discriminate E]);
              exists (S (f + 2)); rewrite unify_type_arguments by (first [reflexivity|apply (fragment_not_variable env); assumption]);
              rewrite ownership_refl; cbn [compare_variances]; first [exact Ff|exact Fbot].
        * (* the same, as far as the reference is concerned *)
          destruct (Hb eq_refl) as [g Hg].
          assert (Ff: unify env (f + g) iy ix (Ongoing s) = Some (Ongoing s)) by (apply (unify_fuel_monotone env f); [lia|exact Hf]).
          assert (Fb: unify env (f + g) ix iy (Ongoing s) = Some (Ongoing s)) by (apply (unify_fuel_monotone env g); [lia|exact Hg]).
          clearbody ix iy.
          split; [exact Hfx|]. split; [exact Hfy|].
          split; [|intros _]; exists (S (f + g));
              rewrite unify_type_arguments by (apply (fragment_not_variable env); assumption);
              rewrite ownership_refl; destruct w; cbn [compare_variances];
              first [rewrite Ff; exact Fb|rewrite Fb; exact Ff|exact Ff|exact Fb].
Qed.

Lemma read_class_shaped: forall b t, class_shaped (instantiate env b t) -> read_member b t = instantiate env b t.
Proof.
    intros b t Hs. unfold read_member. destruct Hs as [[m [c [args E]]]|[m [c [args E]]]]; rewrite E; reflexivity.
Qed.

Lemma mentions_member: forall c b f, member_template c f = true ->
    mentions_loosely_bound_in_arguments b f = mentions_loosely_bound b f.
Proof.
    intros c b f Ht. destruct (member_cases c f Ht) as [[m [d [args ->]]]|[m [d [args [-> _]]]]]; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Components of intersections                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* A component of an intersection a member is typed as: a class type as above, or a type parameter
   of the class, of any mutability given to it or narrowed *)
Definition member_component (c: Class) (C: EType): bool :=
    match C with
    | Generic g => existsb (param_eqb (param_of g)) (parameter_ids env c)
    | _ => member_template c C
    end.

(* The instances of a component, through the object and through the reference: through the object,
   a class type; through the reference, one above it, and below it, too, where the reference doesn't
   widen it; or a type argument, of a type related to it as the type arguments of the reference are
   to those of the object *)
Lemma component_instances: forall n' s c xs ys C,
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    member_component c C = true ->
    in_fragment env (instantiate env (bindings_of env c xs) C) = true
    /\ not_argument (instantiate env (bindings_of env c xs) C) = true
    /\ ((in_fragment env (instantiate env (bindings_of env c ys) C) = true
         /\ not_argument (instantiate env (bindings_of env c ys) C) = true
         /\ (exists f, unify env f (instantiate env (bindings_of env c ys) C) (instantiate env (bindings_of env c xs) C) (Ongoing s)
                = Some (Ongoing s))
         /\ (mentions_loosely_bound_in_arguments (bindings_of env c ys) C = false ->
             exists f, unify env f (instantiate env (bindings_of env c xs) C) (instantiate env (bindings_of env c ys) C) (Ongoing s)
                = Some (Ongoing s)))
        \/ exists v o Y, instantiate env (bindings_of env c ys) C = TypeArgument v o Y /\ in_fragment env Y = true
            /\ related s v (instantiate env (bindings_of env c xs) C) Y).
Proof.
    intros n' s c xs ys C Hlx Hly Hxs Hys H HC.
    assert (Hna: forall t, in_fragment env t = true -> not_argument t = true)
        by (intros t Ht; destruct (fragment_cases env t Ht) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; reflexivity).
    destruct C as [m d args|C'|g|me msg|v0 o0 n0|g|cs]; cbn [member_component] in HC;
        try (destruct (proj1 (member_instances n' s c xs ys Hlx Hly Hxs Hys H (depth _)) _ (le_n _) HC)
                as [[Hfx [Hfy [Hup Hdown]]] _];
             split; [exact Hfx|]; split; [exact (Hna _ Hfx)|]; left;
             split; [exact Hfy|]; split; [exact (Hna _ Hfy)|]; split; [exact Hup|];
             intros Hm; apply Hdown; rewrite <- (mentions_member c _ _ HC); exact Hm);
        try (simpl in HC; discriminate HC).
    (* a type parameter of the class *)
    destruct (member_parameter c (param_of g) HC) as [i Hi].
    destruct (nth_error_same_length _ xs i _ (eq_sym Hlx) Hi) as [x Ex].
    destruct (nth_error_same_length _ ys i _ (eq_sym Hly) Hi) as [y Ey].
    pose proof (Hxs x (nth_error_In _ _ Ex)) as Hex.
    destruct (exact_argument_facts x Hex) as [ox [X [-> [HX [_ Hlx']]]]].
    pose proof (Hys y (nth_error_In _ _ Ey)) as Hy.
    destruct y as [| | | |vy oy Y| |]; simpl in Hy; try discriminate Hy.
    pose proof (Forall2_nth_error _ xs ys i _ _ H Ex Ey) as E.
    destruct n' as [|n'']; [discriminate E|].
    rewrite unify_type_arguments in E by (apply (fragment_not_variable env); exact Hy).
    destruct (ownership_is_assignable_to ox oy); [|discriminate E].
    pose proof (lookup_parameter env wf c xs i (param_of g) _ Hi Ex) as Lx.
    pose proof (lookup_parameter env wf c ys i (param_of g) _ Hi Ey) as Ly.
    pose proof (related_inst_ref g s vy X Y HX Hy (related_of_compare n'' s vy X Y HX Hy E)) as Hrel.
    pose proof (inst_ref_in_fragment env g X HX) as HX'. pose proof (inst_ref_in_fragment env g Y Hy) as HY'.
    rewrite (instantiate_bound_reference _ g _ _ _ Lx HX), (instantiate_bound_reference _ g _ _ _ Ly Hy).
    unfold final_argument. rewrite (fragment_not_nesting _ HX'), (fragment_not_nesting _ HY'), !orb_false_r.
    change (is_loose (TypeArgument Model.invariant ox (inst_ref env g X))) with (is_loose (TypeArgument Model.invariant ox X)).
    rewrite Hlx'. split; [exact HX'|]. split; [exact (Hna _ HX')|].
    destruct (is_loose (TypeArgument vy oy (inst_ref env g Y))) eqn:El.
    - right. exists vy, oy, (inst_ref env g Y). split; [reflexivity|]. split; [exact HY'|exact Hrel].
    - left. assert (Hv: vy = Model.invariant) by (destruct vy; first [reflexivity|discriminate El]). subst vy.
      destruct Hrel as [Hup Hdown]. split; [exact HY'|]. split; [exact (Hna _ HY')|].
      split; [exact (Hup ltac:(discriminate))|intros _; exact (Hdown ltac:(discriminate))].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type of the member of the object can be read as the type through the reference *)
Lemma member_read: forall n s m c xs m' ys f,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing s) = Some (Ongoing s) ->
    member_type c f = true ->
    in_fragment env (read_member (bindings_of env c xs) f) = true
    /\ in_fragment env (read_member (bindings_of env c ys) f) = true
    /\ exists fuel, unify env fuel (read_member (bindings_of env c ys) f) (read_member (bindings_of env c xs) f) (Ongoing s)
        = Some (Ongoing s).
Proof.
    intros n s m c xs m' ys f Hc Hlx Hly Hxs Hys H Hf.
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true)
        by (intros x Hx; destruct (exact_argument_facts x (Hxs x Hx)) as [? [? [_ [_ [? _]]]]]; assumption).
    destruct (receiver_arguments n s m c xs m' ys Hc ltac:(lia) Hfxs Hys H) as [n' [-> Hpairs]].
    unfold member_type in Hf. destruct (leaf_parameter f) as [p|] eqn:Hleaf.
    - destruct (leaf_cases f p Hleaf) as [g [nl [-> <-]]].
      destruct (parameter_member n' s c xs ys (param_of g) Hlx Hly Hxs Hys Hpairs Hf)
          as [o [X [v [oy [Y [n'' [Ex [Ey [HX [HY [-> Hcmp]]]]]]]]]]].
      destruct (related_inst_ref g s v X Y HX HY (related_of_compare n'' s v X Y HX HY Hcmp)) as [Hup Hdown].
      pose proof (inst_ref_in_fragment env g X HX) as HX'. pose proof (inst_ref_in_fragment env g Y HY) as HY'.
      destruct nl; cbn [wrap_leaf].
      + (* a nullable type parameter *)
        rewrite (proj2 (read_member_reference _ g _ _ _ Ex HX)), (proj2 (read_member_reference _ g _ _ _ Ey HY)).
        cbn [read_type].
        split; [apply rewrap_in_fragment; exact HX'|].
        destruct v; cbn [read_type].
        * split; [apply rewrap_in_fragment; exact HY'|]. destruct (Hup ltac:(discriminate)) as [k Hk].
          exists (S k). apply rewrap_mono; assumption.
        * split; [exact (top_in_fragment env wf)|]. exists 2. apply top_above; [apply rewrap_in_fragment; exact HX'|lia].
        * split; [apply rewrap_in_fragment; exact HY'|]. destruct (Hup ltac:(discriminate)) as [k Hk].
          exists (S k). apply rewrap_mono; assumption.
      + (* a type parameter *)
        rewrite (proj1 (read_member_reference _ g _ _ _ Ex HX)), (proj1 (read_member_reference _ g _ _ _ Ey HY)).
        cbn [read_type].
        destruct v; cbn [read_type].
        * split; [exact HX'|]. split; [exact HY'|]. exact (Hup ltac:(discriminate)).
        * split; [exact HX'|]. split; [exact (top_in_fragment env wf)|]. exists 2. apply top_above; [exact HX'|lia].
        * split; [exact HX'|]. split; [exact HY'|]. exact (Hup ltac:(discriminate)).
    - (* a class type *)
      rewrite !read_class_shaped by (apply (member_instance_shape c); exact Hf).
      destruct (proj1 (member_instances n' s c xs ys Hlx Hly Hxs Hys Hpairs (depth f)) f (le_n _) Hf)
          as [[Hfx [Hfy [Hfw _]]] _].
      split; [exact Hfx|]. split; [exact Hfy|]. exact Hfw.
Qed.

(*
 * Reading a member through a reference is sound: what the member of the object holds is assignable
 * to what is read through the reference.
 *)
Theorem member_read_sound: forall n s m c xs m' ys f V fuel,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing s) = Some (Ongoing s) ->
    member_type c f = true ->
    in_fragment env V = true ->
    unify env fuel (read_member (bindings_of env c xs) f) V (Ongoing s) = Some (Ongoing s) ->
    exists fuel', unify env fuel' (read_member (bindings_of env c ys) f) V (Ongoing s) = Some (Ongoing s).
Proof.
    intros n s m c xs m' ys f V fuel Hc Hlx Hly Hxs Hys H Hf HV HVx.
    destruct (member_read n s m c xs m' ys f Hc Hlx Hly Hxs Hys H Hf) as [Hfx [Hfy [k Hk]]].
    exists (fuel + k).
    apply (proj1 (transitivity_with_arguments env wf (fuel + k)) V (read_member (bindings_of env c xs) f)
        (read_member (bindings_of env c ys) f) fuel k s); auto.
Qed.

(*
 * Writing a member through a reference is sound: what is assignable to the member through the
 * reference is assignable to the member of the object; or null, to a nullable member.
 *)
Theorem member_write_sound: forall n s m c xs m' ys f V fuel,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing s) = Some (Ongoing s) ->
    member_type c f = true ->
    in_fragment env V = true -> is_non_nullable_nothing env V = false ->
    unify env fuel (write_member (bindings_of env c ys) f) V (Ongoing s) = Some (Ongoing s) ->
    (exists fuel', unify env fuel' (read_member (bindings_of env c xs) f) V (Ongoing s) = Some (Ongoing s))
    \/ (holds_only_null V = true /\ is_nullable env (read_member (bindings_of env c xs) f) = true).
Proof.
    intros n s m c xs m' ys f V fuel Hc Hlx Hly Hxs Hys H Hf HV HVn HW.
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true)
        by (intros x Hx; destruct (exact_argument_facts x (Hxs x Hx)) as [? [? [_ [_ [? _]]]]]; assumption).
    destruct (receiver_arguments n s m c xs m' ys Hc ltac:(lia) Hfxs Hys H) as [n' [-> Hpairs]].
    unfold member_type in Hf. destruct (leaf_parameter f) as [p|] eqn:Hleaf.
    - destruct (leaf_cases f p Hleaf) as [g [nl [-> <-]]].
      destruct (parameter_member n' s c xs ys (param_of g) Hlx Hly Hxs Hys Hpairs Hf)
          as [o [X [v [oy [Y [n'' [Ex [Ey [HX [HY [-> Hcmp]]]]]]]]]]].
      destruct (related_inst_ref g s v X Y HX HY (related_of_compare n'' s v X Y HX HY Hcmp)) as [_ Hdown].
      pose proof (inst_ref_in_fragment env g X HX) as HX'. pose proof (inst_ref_in_fragment env g Y HY) as HY'.
      assert (HXY: Variance_beq v output = false ->
          exists k, unify env k (inst_ref env g X) (inst_ref env g Y) (Ongoing s) = Some (Ongoing s))
          by (intros Hv; apply Hdown; intros ->; discriminate Hv).
      clear Hdown. unfold write_member in HW.
      destruct nl; cbn [wrap_leaf mentions_loosely_bound_in_arguments] in HW |- *.
      + (* a nullable type parameter: takes null for an out-variant type argument, too *)
        change (instantiate env (bindings_of env c ys) (Nullable (Generic g)))
            with (rewrap_nullable (instantiate env (bindings_of env c ys) (Generic g))) in HW.
        rewrite (instantiate_bound_reference _ g _ _ _ Ey HY) in HW.
        destruct (nullable_final_argument_target fuel v oy _ V s HV HY' HW) as [fuel1 HW1]. clear HW fuel. rename HW1 into HW, fuel1 into fuel.
        rewrite (proj2 (read_member_reference _ g _ _ _ Ex HX)). cbn [read_type].
        change (rewrap_nullable (TypeArgument v oy (inst_ref env g Y))) with (Nullable (TypeArgument v oy (inst_ref env g Y))) in HW.
        destruct fuel as [|fuel]; [discriminate HW|].
        destruct (fragment_cases env V HV) as [[mv [cv [vargs ->]]]|[mv [cv [vargs [-> HV']]]]].
        * rewrite unify_nullable_class in HW. destruct fuel as [|fuel]; [discriminate HW|].
          rewrite (unify_argument_value fuel v oy _ _ s HV) in HW.
          destruct (Variance_beq v output) eqn:Hv; [rewrite HVn in HW; discriminate HW|].
          destruct (HXY eq_refl) as [k Hk].
          left. exists (S (fuel + k)). apply rewrap_above; [exact HX'|exact HV|].
          apply (proj1 (transitivity_with_arguments env wf (fuel + k)) _ (inst_ref env g Y) _ fuel k s); auto.
        * rewrite unify_nullable_nullable in HW. destruct fuel as [|fuel]; [discriminate HW|].
          rewrite (unify_argument_value fuel v oy _ _ s HV') in HW.
          destruct (Variance_beq v output) eqn:Hv.
          -- right. destruct (is_non_nullable_nothing env (RootResolved mv cv vargs)) eqn:En; [|discriminate HW].
             split; [exact En|apply rewrap_is_nullable].
          -- destruct (HXY eq_refl) as [k Hk].
             left. exists (S (fuel + k)).
             change (Nullable (RootResolved mv cv vargs)) with (rewrap_nullable (RootResolved mv cv vargs)).
             apply rewrap_mono; [exact HV'|exact HX'|].
             apply (proj1 (transitivity_with_arguments env wf (fuel + k)) _ (inst_ref env g Y) _ fuel k s); auto.
      + (* a type parameter: an out-variant type argument takes nothing but Nothing *)
        left. rewrite (instantiate_bound_reference _ g _ _ _ Ey HY) in HW.
        destruct (final_argument_target fuel v oy _ V s HV HY' HW) as [fuel1 HW1]. clear HW fuel. rename HW1 into HW, fuel1 into fuel.
        rewrite (proj1 (read_member_reference _ g _ _ _ Ex HX)). cbn [read_type].
        destruct fuel as [|fuel]; [discriminate HW|]. rewrite (unify_argument_value fuel v oy _ V s HV) in HW.
        destruct (Variance_beq v output) eqn:Hv; [rewrite HVn in HW; discriminate HW|].
        destruct (HXY eq_refl) as [k Hk].
        exists (fuel + k). apply (proj1 (transitivity_with_arguments env wf (fuel + k)) V (inst_ref env g Y) _ fuel k s); auto.
    - (* a class type *)
      left. rewrite read_class_shaped by (apply (member_instance_shape c); exact Hf).
      destruct (proj1 (member_instances n' s c xs ys Hlx Hly Hxs Hys Hpairs (depth f)) f (le_n _) Hf)
          as [[Hfx [Hfy [_ Hback]]] _].
      unfold write_member in HW. rewrite (mentions_member c _ _ Hf) in HW.
      destruct (mentions_loosely_bound (bindings_of env c ys) f) eqn:Em.
      + destruct (member_cases c f Hf) as [[m0 [d0 [a0 ->]]]|[m0 [d0 [a0 [-> _]]]]].
        * (* a class type: takes nothing but Nothing, which is assignable to the member of the object *)
          exists (fuel + 2).
          exact (proj1 (transitivity_with_arguments env wf (fuel + 2)) V bottom_type _ fuel 2 s (le_n _)
              HV (bottom_in_fragment env wf) Hfx HW (bottom_below _ 2 s Hfx (le_n _))).
        * (* a nullable class type: takes nothing but null and Nothing *)
          rewrite (instantiate_nullable_class env _ m0 d0 a0) in Hfx |- *.
          assert (Hfx': in_fragment env (RootResolved m0 d0 (map (instantiate env (bindings_of env c xs)) a0)) = true)
              by (change (is_class (RootResolved m0 d0 (map (instantiate env (bindings_of env c xs)) a0))
                      && in_fragment env (RootResolved m0 d0 (map (instantiate env (bindings_of env c xs)) a0)) = true) in Hfx;
                  apply andb_true_iff in Hfx; apply Hfx).
          assert (HN: in_fragment env (Nullable bottom_type) = true)
              by (change (is_class bottom_type && in_fragment env bottom_type = true); rewrite (bottom_in_fragment env wf); reflexivity).
          exists (fuel + 3).
          apply (proj1 (transitivity_with_arguments env wf (fuel + 3)) V (Nullable bottom_type) _ fuel 3 s (le_n _) HV HN Hfx HW).
          rewrite unify_nullable_nullable. apply bottom_below; [exact Hfx'|lia].
      + destruct (Hback eq_refl) as [k Hk]. exists (fuel + k).
        apply (proj1 (transitivity_with_arguments env wf (fuel + k)) V (instantiate env (bindings_of env c ys) f) _ fuel k s);
            auto.
Qed.

End MemberAccess.

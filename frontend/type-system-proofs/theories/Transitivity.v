From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The transitivity of unify, for class types                                                      *)
(*                                                                                                *)
(* If x is assignable to y, and y to z, then x is assignable to z. This is proven for a fragment  *)
(* of the types:                                                                                   *)
(* - class types with as many type arguments as the class has type parameters; the type arguments *)
(*   of any variance and ownership;                                                                *)
(* - nullable class types;                                                                         *)
(* - without type parameters, type variables, intersections or erroneous types;                   *)
(* and for environments where                                                                      *)
(* - the supertypes are transitive, Any has none, and the class hierarchy has no cycles;          *)
(* - the type parameters of a class are distinct, Nothing and Any have none and aren't core        *)
(*   scalars;                                                                                      *)
(* - the type arguments of supertypes are made of type parameters of the subclass, as they are     *)
(*   (`T`: invariant, of the ownership of T), and of class types with type arguments of an explicit *)
(*   ownership: `class Map<K, V> : Iterable<owned Pair<K, V>>`; see template_argument;               *)
(* - the type arguments of a supertype of a supertype are those of the supertype, instantiated     *)
(*   (supertypes_compose).                                                                         *)
(*                                                                                                *)
(* The heart of it is lifting: where each type argument of a reference to a class can stand in for *)
(* the corresponding one of another reference, the type arguments of a supertype, instantiated     *)
(* with the former, can stand in for those instantiated with the latter. That takes the widening   *)
(* that instantiation does (see Subtyping.instantiate): without it, `Map<out K, V>` would be an     *)
(* `Iterable<owned Pair<out K, V>>`, which `Map<K, V>` isn't.                                      *)
(*                                                                                                *)
(* Prescribed ownership (TypeParameterDecl.prescribed_ownership) is carried over to the supertypes,*)
(* if the supertypes repeat it; see prescriptions_carry_over_to_supertypes.                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* Lists                                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma Forall2_impl_in: forall {A B: Type} (R S: A -> B -> Prop) l l',
    Forall2 R l l' -> (forall a b, In a l -> In b l' -> R a b -> S a b) -> Forall2 S l l'.
Proof.
    intros A B R S l l' H. induction H as [|a b l l' Hab H IH]; intros Himpl; constructor.
    - apply Himpl; [left|left|]; auto.
    - apply IH. intros a' b' Ha Hb. apply Himpl; right; assumption.
Qed.

Lemma Forall2_nth_error: forall {A B: Type} (R: A -> B -> Prop) l l' k a b,
    Forall2 R l l' -> nth_error l k = Some a -> nth_error l' k = Some b -> R a b.
Proof.
    intros A B R l l' k a b H. revert k. induction H as [|a' b' l l' Hab H IH]; intros [|k] Ha Hb;
        simpl in Ha, Hb; try discriminate.
    - injection Ha as <-. injection Hb as <-. exact Hab.
    - exact (IH k Ha Hb).
Qed.

Lemma Forall2_map_same: forall {A B: Type} (R: B -> B -> Prop) (f g: A -> B) l,
    (forall a, In a l -> R (f a) (g a)) -> Forall2 R (map f l) (map g l).
Proof.
    intros A B R f g l H. induction l as [|a l IH]; simpl; constructor.
    - apply H. left. reflexivity.
    - apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma nth_error_same_length: forall {A B: Type} (l: list A) (l': list B) k a,
    length l = length l' -> nth_error l k = Some a -> exists b, nth_error l' k = Some b.
Proof.
    intros A B l l' k a Hl H. destruct (nth_error l' k) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. assert (k < length l) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma existsb_or_map: forall {A B: Type} (f g: A -> bool) (h: B -> bool) (k: A -> B) l,
    (forall a, In a l -> f a = g a || h (k a)) -> existsb f l = existsb g l || existsb h (map k l).
Proof.
    intros A B f g h k l H. induction l as [|a l IH]; simpl; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH by (intros a' Ha'; apply H; right; exact Ha').
    destruct (g a), (h (k a)), (existsb g l), (existsb h (map k l)); reflexivity.
Qed.

Section Transitivity.

Variable env: Environment.

Definition parameter_ids (c: Class): list TypeParameterId := map param_id (type_parameters (declaration_of env c)).

Definition is_class (t: EType): bool :=
    match t with RootResolved _ _ _ => true | _ => false end.

Fixpoint in_fragment (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        Nat.eqb (length arguments) (length (parameter_ids c))
        && forallb (fun a => match a with TypeArgument _ _ n => in_fragment n | _ => false end) arguments
    | Nullable n => is_class n && in_fragment n
    | _ => false
    end.

Definition argument_in_fragment (a: EType): bool :=
    match a with TypeArgument _ _ n => in_fragment n | _ => false end.

Fixpoint depth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments =>
        S (list_max (map (fun a => match a with TypeArgument _ _ n => S (depth n) | _ => 0 end) arguments))
    | Nullable n => S (depth n)
    | _ => 0
    end.

Definition argument_depth (a: EType): nat :=
    match a with TypeArgument _ _ n => S (depth n) | _ => 0 end.

(* BoundTypeArgument.unify, once the ownerships are found to fit *)
Definition compare_variances (u: UnifyFn) (target_variance assignee_variance: Variance) (target assignee: EType) (s: VariableStates): option Unification :=
    match target_variance, assignee_variance with
    | invariant, invariant => match u target assignee (Ongoing s) with Some c => u assignee target c | None => None end
    | invariant, _ => Some Failed
    | output, output | output, invariant => u target assignee (Ongoing s)
    | output, input => u target top_type (Ongoing s)
    | input, input | input, invariant => u assignee target (Ongoing s)
    | input, output => u bottom_type target (Ongoing s)
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* The form of supertypes                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Definition is_parameter_ownership (o: Ownership): bool :=
    match o with parameter_ownership _ => true | _ => false end.

(* The type parameter a type argument is, as it is: `T` *)
Definition template_parameter (t: EType): option TypeParameterId :=
    match t with
    | TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p' _)) =>
        if param_eqb p p' then Some p else None
    | _ => None
    end.

(* A type in the type arguments of a supertype of `sub`: a class type, whose type arguments are type
   parameters of `sub`, or of an explicit ownership and of such a type *)
Fixpoint template_type (sub: Class) (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        Nat.eqb (length arguments) (length (parameter_ids c))
        && forallb (fun a =>
            match template_parameter a with
            | Some p => existsb (param_eqb p) (parameter_ids sub)
            | None =>
                match a with
                | TypeArgument _ o n => negb (is_parameter_ownership o) && template_type sub n
                | _ => false
                end
            end) arguments
    | Nullable n => is_class n && template_type sub n
    | _ => false
    end.

Definition template_argument (sub: Class) (a: EType): bool :=
    match template_parameter a with
    | Some p => existsb (param_eqb p) (parameter_ids sub)
    | None =>
        match a with
        | TypeArgument _ o n => negb (is_parameter_ownership o) && template_type sub n
        | _ => false
        end
    end.

(* The type arguments of `super` as a supertype of `sub`, in terms of the type parameters of `sub` *)
Definition supertype_arguments (sub super: Class): list EType :=
    match parameterized_supertype env sub super with
    | RootResolved _ _ arguments => arguments
    | _ => []
    end.

Hypothesis supertypes_are_transitive: forall a b c,
    In b (supertypes_of env a) -> In c (supertypes_of env b) -> In c (supertypes_of env a).
Hypothesis any_has_no_supertypes: supertypes_of env any = [].
Hypothesis acyclic: forall c c',
    base_type_is_subtype_of env c c' = true -> base_type_is_subtype_of env c' c = true -> c = c'.
Hypothesis parameter_ids_are_distinct: forall c, NoDup (parameter_ids c).
Hypothesis nothing_has_no_type_parameters: parameter_ids nothing = [].
Hypothesis any_has_no_type_parameters: parameter_ids any = [].
Hypothesis nothing_is_no_scalar: is_core_scalar (declaration_of env nothing) = false.
Hypothesis any_is_no_scalar: is_core_scalar (declaration_of env any) = false.
Hypothesis supertypes_are_templates: forall sub super,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length (supertype_arguments sub super) = length (parameter_ids super)
    /\ forall t, In t (supertype_arguments sub super) -> template_argument sub t = true.
Hypothesis supertypes_compose: forall a b c,
    a <> b -> b <> c -> a <> c -> a <> nothing -> b <> nothing ->
    base_type_is_subtype_of env a b = true -> base_type_is_subtype_of env b c = true ->
    supertype_arguments a c = map (instantiate env (bindings_of env b (supertype_arguments a b))) (supertype_arguments b c).

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about classes, mutabilities and ownerships                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma class_eqb_true: forall a b, class_eqb a b = true -> a = b.
Proof. intros a b. unfold class_eqb. destruct (Class_eq_dec a b); congruence. Qed.

Lemma class_eqb_false_neq: forall a b, class_eqb a b = false -> a <> b.
Proof. intros a b H ->. rewrite class_eqb_refl in H. discriminate H. Qed.

Lemma base_type_is_subtype_of_iff: forall sub super,
    base_type_is_subtype_of env sub super = true <->
    super = sub \/ super = any \/ (super <> nothing /\ (sub = nothing \/ In super (supertypes_of env sub))).
Proof.
    intros sub super. unfold base_type_is_subtype_of.
    destruct (class_eqb super sub) eqn:E1; [apply class_eqb_true in E1; split; auto|apply class_eqb_false_neq in E1].
    destruct (class_eqb super any) eqn:E2; [apply class_eqb_true in E2; split; auto|apply class_eqb_false_neq in E2].
    destruct (class_eqb super nothing) eqn:E3.
    { apply class_eqb_true in E3. split; [discriminate|]. intros [H|[H|[H _]]]; contradiction. }
    apply class_eqb_false_neq in E3.
    destruct (class_eqb sub nothing) eqn:E4; [apply class_eqb_true in E4; split; auto|apply class_eqb_false_neq in E4].
    rewrite existsb_exists. split.
    - intros [c [Hin Hc]]. apply class_eqb_true in Hc. subst c. auto.
    - intros [H|[H|[_ [H|Hin]]]]; try contradiction. exists super. split; [exact Hin|apply class_eqb_refl].
Qed.

Lemma base_type_is_subtype_of_trans: forall a b c,
    base_type_is_subtype_of env a b = true -> base_type_is_subtype_of env b c = true ->
    base_type_is_subtype_of env a c = true.
Proof.
    intros a b c Hab Hbc. apply base_type_is_subtype_of_iff in Hab, Hbc. apply base_type_is_subtype_of_iff.
    destruct Hbc as [->|[->|[Hc [Hb|Hin]]]]; [exact Hab|right; left; reflexivity| |].
    - subst b. destruct Hab as [Ha|[Hb|[Hb _]]]; [|discriminate Hb|contradiction].
      right. right. split; [exact Hc|]. left. symmetry. exact Ha.
    - destruct Hab as [Hb|[Hb|[_ [Ha|Hin']]]].
        + subst b. right. right. split; [exact Hc|]. right. exact Hin.
        + subst b. rewrite any_has_no_supertypes in Hin. contradiction.
        + right. right. split; [exact Hc|]. left. exact Ha.
        + right. right. split; [exact Hc|]. right. exact (supertypes_are_transitive _ _ _ Hin' Hin).
Qed.

Lemma nothing_is_below_all: forall c, base_type_is_subtype_of env nothing c = true.
Proof.
    intros c. apply base_type_is_subtype_of_iff.
    destruct (Class_eq_dec c nothing) as [->|Hc]; [left; reflexivity|]. right. right. auto.
Qed.

Lemma only_nothing_is_below_nothing: forall c, base_type_is_subtype_of env c nothing = true -> c = nothing.
Proof. intros c H. apply base_type_is_subtype_of_iff in H. destruct H as [H|[H|[H _]]]; [auto|discriminate H|contradiction]. Qed.

Lemma mutability_trans: forall a b c,
    Model.is_subtype_of a b = true -> Model.is_subtype_of b c = true -> Model.is_subtype_of a c = true.
Proof. intros [] [] [] H1 H2; simpl in *; congruence. Qed.

Lemma ownership_trans: forall a b c,
    ownership_is_assignable_to a b = true -> ownership_is_assignable_to b c = true -> ownership_is_assignable_to a c = true.
Proof.
    intros [| | |p] [| | |q] [| | |r] H1 H2; simpl in *; try discriminate; try reflexivity.
    apply param_eqb_eq in H1, H2. subst. apply param_eqb_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the fragment                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma root_in_fragment: forall m c arguments,
    in_fragment (RootResolved m c arguments) = true ->
    length arguments = length (parameter_ids c) /\ forall a, In a arguments -> argument_in_fragment a = true.
Proof.
    intros m c arguments H.
    change (Nat.eqb (length arguments) (length (parameter_ids c)) && forallb argument_in_fragment arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hl Ha]. split; [apply Nat.eqb_eq, Hl|apply forallb_forall, Ha].
Qed.

Lemma fragment_cases: forall t, in_fragment t = true ->
    (exists m c arguments, t = RootResolved m c arguments) \/
    (exists m c arguments, t = Nullable (RootResolved m c arguments) /\ in_fragment (RootResolved m c arguments) = true).
Proof.
    intros [m c arguments|[m c arguments| | | | | |]| | | | |] H; simpl in H; try discriminate H.
    - left. exists m, c, arguments. reflexivity.
    - right. exists m, c, arguments. split; [reflexivity|exact H].
Qed.

Definition is_type_argument (t: EType): bool :=
    match t with TypeArgument _ _ _ => true | _ => false end.

Lemma argument_in_fragment_is_type_argument: forall a, argument_in_fragment a = true -> is_type_argument a = true.
Proof. intros [| | | | | |] H; simpl in H; try discriminate H; reflexivity. Qed.

Lemma depth_nullable: forall t, depth (Nullable t) = S (depth t).
Proof. reflexivity. Qed.

Lemma argument_depth_below: forall m c arguments a,
    In a arguments -> S (argument_depth a) <= depth (RootResolved m c arguments).
Proof.
    intros m c arguments a Ha. change (S (argument_depth a) <= S (list_max (map argument_depth arguments))).
    assert (H: Forall (fun k => k <= list_max (map argument_depth arguments)) (map argument_depth arguments))
        by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (argument_depth a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma bottom_in_fragment: in_fragment bottom_type = true.
Proof.
    change (Nat.eqb (length (@nil EType)) (length (parameter_ids nothing)) && forallb argument_in_fragment [] = true).
    rewrite nothing_has_no_type_parameters. reflexivity.
Qed.

Lemma top_in_fragment: in_fragment top_type = true.
Proof.
    change (is_class (RootResolved (Some readonly) any []) && (Nat.eqb (length (@nil EType)) (length (parameter_ids any)) && forallb argument_in_fragment []) = true).
    rewrite any_has_no_type_parameters. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify on the fragment, one step                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_classes: forall n mt ct targs ma ca aargs s,
    unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) =
    if base_type_is_subtype_of env ca ct then
        if Model.is_subtype_of (mutability_of env (RootResolved ma ca aargs)) (mutability_of env (RootResolved mt ct targs))
        then if class_eqb ca nothing then Some (Ongoing s)
            else unify_arguments (unify env n) targs
                (if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) s
        else Some Failed
    else Some Failed.
Proof.
    intros. rewrite unify_step_once. unfold unify_step, unify_root_resolved.
    destruct (base_type_is_subtype_of env ca ct); [|reflexivity]. cbn [negb].
    destruct (Model.is_subtype_of _ _); reflexivity.
Qed.

Lemma mutability_of_class: forall m c arguments arguments',
    mutability_of env (RootResolved m c arguments) = mutability_of env (RootResolved m c arguments').
Proof. reflexivity. Qed.

Lemma unify_class_nullable: forall n m c arguments na s,
    unify env (S n) (RootResolved m c arguments) (Nullable na) (Ongoing s) = Some Failed.
Proof. reflexivity. Qed.

Lemma unify_nullable_class: forall n nt m c arguments s,
    unify env (S n) (Nullable nt) (RootResolved m c arguments) (Ongoing s) = unify env n nt (RootResolved m c arguments) (Ongoing s).
Proof. reflexivity. Qed.

Lemma unify_nullable_nullable: forall n nt na s,
    unify env (S n) (Nullable nt) (Nullable na) (Ongoing s) = unify env n nt na (Ongoing s).
Proof. reflexivity. Qed.

Lemma unify_type_arguments: forall n vt ot nt va oa na s,
    unify env (S n) (TypeArgument vt ot nt) (TypeArgument va oa na) (Ongoing s) =
    if ownership_is_assignable_to oa ot then compare_variances (unify env n) vt va nt na s else Some Failed.
Proof.
    intros. rewrite unify_step_once. unfold unify_step, unify_type_argument. cbn beta iota zeta.
    destruct (ownership_is_assignable_to oa ot); [|reflexivity]. destruct vt, va; reflexivity.
Qed.

Lemma fold_stays_failed: forall n l,
    fold_unify (fun inner '(t, a) => unify env n t a inner) l Failed = Some Failed.
Proof. intros n l. induction l as [|[t a] rest IH]; simpl; [reflexivity|]. rewrite unify_keeps_failure. exact IH. Qed.

(* Both ways of an invariant comparison *)
Lemma both_ways: forall (u: UnifyFn) t a s,
    (forall x y, u x y Failed = Some Failed) ->
    (forall w, u t a (Ongoing s) = Some (Ongoing w) -> w = s) ->
    match u t a (Ongoing s) with Some c => u a t c | None => None end = Some (Ongoing s) ->
    u t a (Ongoing s) = Some (Ongoing s) /\ u a t (Ongoing s) = Some (Ongoing s).
Proof.
    intros u t a s Hf Hk H. destruct (u t a (Ongoing s)) as [[w|]|] eqn:E.
    - pose proof (Hk w eq_refl). subst w. auto.
    - rewrite Hf in H. discriminate H.
    - discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Templates: the type arguments of supertypes                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma template_parameter_some: forall t p,
    template_parameter t = Some p -> exists bp, t = TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp)).
Proof.
    intros [| | | |v o n| |] p H; simpl in H; try discriminate H.
    destruct v; simpl in H; try discriminate H. destruct o as [| | |q]; simpl in H; try discriminate H.
    destruct n as [| |[[gm|] p' bp]| | | |]; simpl in H; try discriminate H.
    destruct (param_eqb q p') eqn:E; [|discriminate H]. injection H as <-. apply param_eqb_eq in E. subst p'.
    exists bp. reflexivity.
Qed.

Lemma template_kind: forall sub t,
    template_argument sub t = true ->
    (exists p bp k, t = TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))
        /\ nth_error (parameter_ids sub) k = Some p)
    \/ (exists v o n, t = TypeArgument v o n /\ template_parameter t = None
        /\ is_parameter_ownership o = false /\ template_type sub n = true).
Proof.
    intros sub t H. unfold template_argument in H. destruct (template_parameter t) as [p|] eqn:E.
    - left. destruct (template_parameter_some t p E) as [bp ->]. apply existsb_exists in H.
      destruct H as [q [Hq Hpq]]. apply param_eqb_eq in Hpq. subst q.
      apply In_nth_error in Hq. destruct Hq as [k Hk]. exists p, bp, k. auto.
    - right. destruct t as [| | | |v o n| |]; try discriminate H.
      apply andb_true_iff in H. destruct H as [Ho Hn]. exists v, o, n.
      repeat split; auto. destruct o; auto; discriminate Ho.
Qed.

Lemma template_is_type_argument: forall sub t, template_argument sub t = true -> is_type_argument t = true.
Proof.
    intros sub t H. destruct (template_kind sub t H) as [[p [bp [k [-> _]]]]|[v [o [n [-> _]]]]]; reflexivity.
Qed.

Lemma root_template: forall sub m c arguments,
    template_type sub (RootResolved m c arguments) = true ->
    length arguments = length (parameter_ids c) /\ forall a, In a arguments -> template_argument sub a = true.
Proof.
    intros sub m c arguments H.
    change (Nat.eqb (length arguments) (length (parameter_ids c)) && forallb (template_argument sub) arguments = true) in H.
    apply andb_true_iff in H. destruct H as [Hl Ha]. split; [apply Nat.eqb_eq, Hl|apply forallb_forall, Ha].
Qed.

Lemma template_type_cases: forall sub t, template_type sub t = true ->
    (exists m c arguments, t = RootResolved m c arguments) \/
    (exists m c arguments, t = Nullable (RootResolved m c arguments) /\ template_type sub (RootResolved m c arguments) = true).
Proof.
    intros sub [m c arguments|[m c arguments| | | | | |]| | | | |] H; simpl in H; try discriminate H.
    - left. exists m, c, arguments. reflexivity.
    - right. exists m, c, arguments. split; [reflexivity|exact H].
Qed.

Lemma template_argument_depth: forall sub a, template_argument sub a = true -> 1 <= argument_depth a.
Proof. intros sub a H. destruct (template_kind sub a H) as [[p [bp [k [-> _]]]]|[v [o [n [-> _]]]]]; simpl; lia. Qed.

Lemma template_type_depth: forall sub t, template_type sub t = true -> 1 <= depth t.
Proof.
    intros sub t H. destruct (template_type_cases sub t H) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]];
        simpl; lia.
Qed.

Lemma lookup_in_bindings: forall ids ys k p y,
    NoDup ids -> nth_error ids k = Some p -> nth_error ys k = Some y -> lookup_binding (combine ids ys) p = Some y.
Proof.
    intros ids. induction ids as [|i ids IH]; intros ys k p y Hnd Hi Hy; [destruct k; discriminate Hi|].
    destruct ys as [|y0 ys]; [destruct k; discriminate Hy|]. inversion Hnd as [|? ? Hnotin Hnd']. subst.
    destruct k as [|k]; simpl in Hi, Hy |- *.
    - injection Hi as ->. injection Hy as ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p i) eqn:E.
      + apply param_eqb_eq in E. subst i. exfalso. apply Hnotin. eapply nth_error_In. exact Hi.
      + exact (IH ys k p y Hnd' Hi Hy).
Qed.

Lemma lookup_parameter: forall sub ys k p y,
    nth_error (parameter_ids sub) k = Some p -> nth_error ys k = Some y ->
    lookup_binding (bindings_of env sub ys) p = Some y.
Proof. intros. apply (lookup_in_bindings (parameter_ids sub) ys k); auto. Qed.

Lemma instantiate_parameter_template: forall bindings p bp y,
    lookup_binding bindings p = Some y -> is_type_argument y = true ->
    instantiate env bindings (TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))) = y.
Proof.
    intros bindings p bp [| | | |vy oy ny| |] H Hy; simpl in Hy; try discriminate Hy.
    simpl. rewrite H. destruct vy; reflexivity.
Qed.

(* The type parameter `T` of `sub`, instantiated with the type arguments of a reference to `sub`, is
   the one in its place *)
Lemma selects: forall sub ys p bp k y,
    nth_error (parameter_ids sub) k = Some p -> nth_error ys k = Some y -> is_type_argument y = true ->
    instantiate env (bindings_of env sub ys) (TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))) = y.
Proof.
    intros sub ys p bp k y Hp Hy Hta. apply instantiate_parameter_template; [|exact Hta].
    exact (lookup_parameter sub ys k p y Hp Hy).
Qed.

Lemma mentions_parameter_template: forall bindings p bp y,
    lookup_binding bindings p = Some y ->
    mentions_loosely_bound bindings (TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))) = is_loose y.
Proof. intros bindings p bp y H. simpl. rewrite H. reflexivity. Qed.

Lemma instantiate_class: forall b m c arguments,
    instantiate env b (RootResolved m c arguments) = RootResolved m c (map (instantiate env b) arguments).
Proof. reflexivity. Qed.

Lemma instantiate_nullable_class: forall b m c arguments,
    instantiate env b (Nullable (RootResolved m c arguments)) = Nullable (RootResolved m c (map (instantiate env b) arguments)).
Proof. reflexivity. Qed.

Lemma mentions_class: forall b m c arguments,
    mentions_loosely_bound b (RootResolved m c arguments) = existsb (mentions_loosely_bound b) arguments.
Proof. reflexivity. Qed.

Definition class_shaped (t: EType): Prop :=
    (exists m c arguments, t = RootResolved m c arguments) \/ (exists m c arguments, t = Nullable (RootResolved m c arguments)).

(* A type argument that isn't a type parameter, instantiated: widened where a type parameter in it is
   bound loosely *)
Lemma instantiate_template_argument: forall b v o n,
    is_parameter_ownership o = false -> class_shaped n ->
    instantiate env b (TypeArgument v o n) =
    if mentions_loosely_bound b n then
        match v with
        | input => TypeArgument input o bottom_type
        | _ => TypeArgument output o (instantiate env b n)
        end
    else TypeArgument v o (instantiate env b n).
Proof.
    intros b v o n Ho [[m [c [arguments ->]]]|[m [c [arguments ->]]]];
        destruct o; try discriminate Ho; destruct v; reflexivity.
Qed.

Lemma template_instance_shape: forall sub b t, template_type sub t = true -> class_shaped (instantiate env b t).
Proof.
    intros sub b t H. destruct (template_type_cases sub t H) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]].
    - left. exists m, c, (map (instantiate env b) arguments). reflexivity.
    - right. exists m, c, (map (instantiate env b) arguments). reflexivity.
Qed.

Lemma template_shape: forall sub t, template_type sub t = true -> class_shaped t.
Proof.
    intros sub t H. destruct (template_type_cases sub t H) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]].
    - left. eauto.
    - right. eauto.
Qed.

(* Instantiating a template with type arguments of the fragment gives a type (argument) of it *)
Lemma template_instances_with_arguments: forall sub ys,
    length ys = length (parameter_ids sub) -> (forall y, In y ys -> argument_in_fragment y = true) ->
    forall k,
    (forall t, depth t <= k -> template_type sub t = true -> in_fragment (instantiate env (bindings_of env sub ys) t) = true)
    /\ (forall a, argument_depth a <= k -> template_argument sub a = true ->
        argument_in_fragment (instantiate env (bindings_of env sub ys) a) = true).
Proof.
    intros sub ys Hl Hys k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth sub t Ht)|pose proof (template_argument_depth sub t Ht)]; lia. }
    assert (Hroot: forall m c arguments, depth (RootResolved m c arguments) <= S k ->
        template_type sub (RootResolved m c arguments) = true ->
        in_fragment (instantiate env (bindings_of env sub ys) (RootResolved m c arguments)) = true).
    { intros m c arguments Hd Ht. destruct (root_template sub m c arguments Ht) as [Hla Hargs].
      rewrite instantiate_class.
      change (Nat.eqb (length (map (instantiate env (bindings_of env sub ys)) arguments)) (length (parameter_ids c))
          && forallb argument_in_fragment (map (instantiate env (bindings_of env sub ys)) arguments) = true).
      rewrite length_map, Hla, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
      destruct Ha' as [a [<- Ha]]. pose proof (argument_depth_below m c arguments a Ha).
      apply IHa; [lia|apply Hargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases sub t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
      + exact (Hroot m c arguments Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class, <- instantiate_class.
        change (is_class (instantiate env (bindings_of env sub ys) (RootResolved m c arguments))
            && in_fragment (instantiate env (bindings_of env sub ys) (RootResolved m c arguments)) = true).
        rewrite (Hroot m c arguments); [reflexivity|lia|exact Ht'].
    - intros a Hd Ha. destruct (template_kind sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        rewrite (selects sub ys p bp i y Hi Hy); [apply Hys; eapply nth_error_In; exact Hy|].
        apply argument_in_fragment_is_type_argument, Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd. rewrite (instantiate_template_argument _ v o n Ho (template_shape sub n Hn)).
        destruct (mentions_loosely_bound _ n); [destruct v|]; simpl;
            first [exact bottom_in_fragment | apply IHt; [lia|exact Hn]].
Qed.

Lemma template_instance_in_fragment: forall sub ys a,
    length ys = length (parameter_ids sub) -> (forall y, In y ys -> argument_in_fragment y = true) ->
    template_argument sub a = true -> argument_in_fragment (instantiate env (bindings_of env sub ys) a) = true.
Proof. intros sub ys a Hl Hys Ha. exact (proj2 (template_instances_with_arguments sub ys Hl Hys _) a (le_n _) Ha). Qed.

Lemma template_type_instance_in_fragment: forall sub ys t,
    length ys = length (parameter_ids sub) -> (forall y, In y ys -> argument_in_fragment y = true) ->
    template_type sub t = true -> in_fragment (instantiate env (bindings_of env sub ys) t) = true.
Proof. intros sub ys t Hl Hys Ht. exact (proj1 (template_instances_with_arguments sub ys Hl Hys _) t (le_n _) Ht). Qed.

Lemma parameterized_supertype_arguments_eq: forall sub arguments super,
    parameterized_supertype_arguments env sub arguments super
    = map (instantiate env (bindings_of env sub arguments)) (supertype_arguments sub super).
Proof.
    intros. unfold parameterized_supertype_arguments, supertype_arguments.
    destruct (parameterized_supertype env sub super); reflexivity.
Qed.

(* A reference to a supertype, as normalized from one to a subclass, is of the fragment *)
Lemma supertype_arguments_in_fragment: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids sub) -> (forall x, In x xs -> argument_in_fragment x = true) ->
    length (parameterized_supertype_arguments env sub xs super) = length (parameter_ids super)
    /\ forall a, In a (parameterized_supertype_arguments env sub xs super) -> argument_in_fragment a = true.
Proof.
    intros sub super xs Hne Hn Hb Hl Hxs. destruct (supertypes_are_templates sub super Hne Hn Hb) as [Hlt Ht].
    rewrite parameterized_supertype_arguments_eq. split; [rewrite length_map; exact Hlt|].
    intros a Ha. apply in_map_iff in Ha. destruct Ha as [t [<- Hin]].
    apply template_instance_in_fragment; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Loose type arguments                                                                            *)
(* ---------------------------------------------------------------------------------------------- *)

(* A type argument of a supertype, instantiated, is loose where it was or it was widened *)
Lemma loose_instance: forall sub ys a,
    length ys = length (parameter_ids sub) -> (forall y, In y ys -> is_type_argument y = true) ->
    template_argument sub a = true ->
    is_loose (instantiate env (bindings_of env sub ys) a) = is_loose a || mentions_loosely_bound (bindings_of env sub ys) a.
Proof.
    intros sub ys a Hl Hys Ha. destruct (template_kind sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
    - destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
      rewrite (selects sub ys p bp i y Hi Hy), (mentions_parameter_template _ p bp y (lookup_parameter sub ys i p y Hi Hy));
          [reflexivity|]. apply Hys. eapply nth_error_In. exact Hy.
    - rewrite (instantiate_template_argument _ v o n Ho (template_shape sub n Hn)).
      change (mentions_loosely_bound (bindings_of env sub ys) (TypeArgument v o n))
          with (mentions_loosely_bound (bindings_of env sub ys) n).
      destruct (mentions_loosely_bound _ n); [destruct v; simpl; rewrite ?orb_true_r; reflexivity|].
      rewrite orb_false_r. reflexivity.
Qed.

(* A loose type argument can only stand in for a loose one *)
Lemma loose_monotone: forall f x y s, argument_in_fragment x = true -> argument_in_fragment y = true ->
    unify env f y x (Ongoing s) = Some (Ongoing s) -> is_loose x = true -> is_loose y = true.
Proof.
    intros [|f] [| | | |vx ox X| |] [| | | |vy oy Y| |] s Hx Hy H Hl; simpl in Hx, Hy; try discriminate.
    rewrite unify_type_arguments in H. destruct vy; [|reflexivity|reflexivity].
    destruct (ownership_is_assignable_to ox oy) eqn:Ho; [|discriminate H].
    destruct vx; unfold compare_variances in H; try discriminate H.
    destruct ox as [| | |p], oy as [| | |q]; simpl in Hl, Ho |- *; congruence.
Qed.

(* Where the type arguments of one reference are loose only where those of another are, so are
   instantiated templates *)
Lemma mentions_monotone_with_arguments: forall sub xs ys,
    length xs = length (parameter_ids sub) -> length ys = length (parameter_ids sub) ->
    Forall2 (fun x y => is_loose x = true -> is_loose y = true) xs ys ->
    forall k,
    (forall t, depth t <= k -> template_type sub t = true ->
        mentions_loosely_bound (bindings_of env sub xs) t = true -> mentions_loosely_bound (bindings_of env sub ys) t = true)
    /\ (forall a, argument_depth a <= k -> template_argument sub a = true ->
        mentions_loosely_bound (bindings_of env sub xs) a = true -> mentions_loosely_bound (bindings_of env sub ys) a = true).
Proof.
    intros sub xs ys Hlx Hly Hloose k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth sub t Ht)|pose proof (template_argument_depth sub t Ht)]; lia. }
    assert (Hroot: forall m c arguments, depth (RootResolved m c arguments) <= S k ->
        template_type sub (RootResolved m c arguments) = true ->
        mentions_loosely_bound (bindings_of env sub xs) (RootResolved m c arguments) = true ->
        mentions_loosely_bound (bindings_of env sub ys) (RootResolved m c arguments) = true).
    { intros m c arguments Hd Ht H. destruct (root_template sub m c arguments Ht) as [_ Hargs].
      rewrite mentions_class in H |- *. apply existsb_exists in H. destruct H as [a [Ha Hm]].
      apply existsb_exists. exists a. split; [exact Ha|].
      pose proof (argument_depth_below m c arguments a Ha). apply IHa; [lia|apply Hargs, Ha|exact Hm]. }
    split.
    - intros t Hd Ht H. destruct (template_type_cases sub t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
      + exact (Hroot m c arguments Hd Ht H).
      + rewrite depth_nullable in Hd. exact (Hroot m c arguments ltac:(lia) Ht' H).
    - intros a Hd Ha H. destruct (template_kind sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ xs i p (eq_sym Hlx) Hi) as [x Hx].
        destruct (nth_error_same_length _ ys i p (eq_sym Hly) Hi) as [y Hy].
        rewrite (mentions_parameter_template _ p bp x (lookup_parameter sub xs i p x Hi Hx)) in H.
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter sub ys i p y Hi Hy)).
        exact (Forall2_nth_error _ xs ys i x y Hloose Hx Hy H).
      + simpl in Hd |- *. apply IHt; [lia|exact Hn|exact H].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating twice: a supertype of a supertype                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma mentions_nullable: forall bindings t,
    mentions_loosely_bound bindings (Nullable t) = mentions_loosely_bound bindings t.
Proof. reflexivity. Qed.

(* A template of `b`, instantiated with the type arguments `sargs` of `b` as a supertype of `a` and
   then with the type arguments `xs` of a reference to `a`, is that template instantiated with
   `sargs` instantiated with `xs`. Widening included: a type argument is widened in one if it is in
   the other. *)
Lemma compose_with_arguments: forall a b xs sargs,
    length xs = length (parameter_ids a) -> (forall x, In x xs -> argument_in_fragment x = true) ->
    length sargs = length (parameter_ids b) -> (forall u, In u sargs -> template_argument a u = true) ->
    forall k,
    (forall t, depth t <= k -> template_type b t = true ->
        mentions_loosely_bound (bindings_of env b (map (instantiate env (bindings_of env a xs)) sargs)) t
            = mentions_loosely_bound (bindings_of env b sargs) t
              || mentions_loosely_bound (bindings_of env a xs) (instantiate env (bindings_of env b sargs) t)
        /\ instantiate env (bindings_of env b (map (instantiate env (bindings_of env a xs)) sargs)) t
            = instantiate env (bindings_of env a xs) (instantiate env (bindings_of env b sargs) t))
    /\ (forall r, argument_depth r <= k -> template_argument b r = true ->
        mentions_loosely_bound (bindings_of env b (map (instantiate env (bindings_of env a xs)) sargs)) r
            = mentions_loosely_bound (bindings_of env b sargs) r
              || mentions_loosely_bound (bindings_of env a xs) (instantiate env (bindings_of env b sargs) r)
        /\ instantiate env (bindings_of env b (map (instantiate env (bindings_of env a xs)) sargs)) r
            = instantiate env (bindings_of env a xs) (instantiate env (bindings_of env b sargs) r)).
Proof.
    intros a b xs sargs Hlx Hxs Hls Hsargs k.
    set (bx := bindings_of env a xs). set (bS := bindings_of env b sargs).
    set (bL := bindings_of env b (map (instantiate env bx) sargs)).
    assert (Hxs': forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply argument_in_fragment_is_type_argument, Hxs, Hx).
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth b t Ht)|pose proof (template_argument_depth b t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type b (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound bL) targs
            = existsb (mentions_loosely_bound bS) targs || existsb (mentions_loosely_bound bx) (map (instantiate env bS) targs)
        /\ map (instantiate env bL) targs = map (instantiate env bx) (map (instantiate env bS) targs)).
    { intros m c targs Hd Ht. destruct (root_template b m c targs Ht) as [_ Hargs]. split.
      - apply existsb_or_map. intros u Hu. pose proof (argument_depth_below m c targs u Hu).
        apply (IHa u); [lia|apply Hargs, Hu].
      - rewrite map_map. apply map_ext_in. intros u Hu. pose proof (argument_depth_below m c targs u Hu).
        apply (IHa u); [lia|apply Hargs, Hu]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases b t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + destruct (Hroot m c targs Hd Ht) as [Hm Hi].
        rewrite (instantiate_class bS), (instantiate_class bL), (instantiate_class bx), !mentions_class, Hi.
        split; [exact Hm|reflexivity].
      + rewrite depth_nullable in Hd. destruct (Hroot m c targs ltac:(lia) Ht') as [Hm Hi].
        rewrite (instantiate_nullable_class bS), (instantiate_nullable_class bL), (instantiate_nullable_class bx),
            !mentions_nullable, !mentions_class, Hi.
        split; [exact Hm|reflexivity].
    - intros r Hd Hr. destruct (template_kind b r Hr) as [[q [bq [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ sargs i q (eq_sym Hls) Hi) as [u Hu].
        pose proof (Hsargs u (nth_error_In _ _ Hu)) as Htu.
        assert (Hu': nth_error (map (instantiate env bx) sargs) i = Some (instantiate env bx u))
            by (rewrite nth_error_map, Hu; reflexivity).
        assert (Hxu: is_type_argument (instantiate env bx u) = true)
            by (apply argument_in_fragment_is_type_argument, template_instance_in_fragment; assumption).
        unfold bL. rewrite (selects b _ q bq i _ Hi Hu' Hxu).
        unfold bS. rewrite (selects b sargs q bq i u Hi Hu (template_is_type_argument a u Htu)).
        rewrite (mentions_parameter_template _ q bq _ (lookup_parameter b _ i q _ Hi Hu')).
        rewrite (mentions_parameter_template _ q bq _ (lookup_parameter b sargs i q u Hi Hu)).
        split; [|reflexivity]. unfold bx. apply loose_instance; assumption.
      + simpl in Hd. destruct (IHt n ltac:(lia) Hn) as [Hm Hi].
        change (mentions_loosely_bound bL (TypeArgument v o n)) with (mentions_loosely_bound bL n).
        change (mentions_loosely_bound bS (TypeArgument v o n)) with (mentions_loosely_bound bS n).
        rewrite (instantiate_template_argument bL v o n Ho (template_shape b n Hn)).
        rewrite (instantiate_template_argument bS v o n Ho (template_shape b n Hn)).
        pose proof (template_instance_shape b bS n Hn) as Hshape.
        destruct (mentions_loosely_bound bS n) eqn:ES.
        * simpl in Hm. rewrite Hm. split; [reflexivity|]. destruct v.
          -- rewrite (instantiate_template_argument bx output o _ Ho Hshape), Hi.
             destruct (mentions_loosely_bound bx (instantiate env bS n)); reflexivity.
          -- rewrite (instantiate_template_argument bx input o bottom_type Ho
                  ltac:(left; exists (Some exclusive), nothing, []; reflexivity)).
             reflexivity.
          -- rewrite (instantiate_template_argument bx output o _ Ho Hshape), Hi.
             destruct (mentions_loosely_bound bx (instantiate env bS n)); reflexivity.
        * simpl in Hm. rewrite Hm, (instantiate_template_argument bx v o _ Ho Hshape), Hi.
          change (mentions_loosely_bound bx (TypeArgument v o (instantiate env bS n)))
              with (mentions_loosely_bound bx (instantiate env bS n)).
          split; reflexivity.
Qed.

(* The type arguments of a supertype of a supertype, as those of a supertype directly *)
Lemma parameterized_supertype_arguments_compose: forall a b c xs,
    a <> b -> b <> c -> a <> c -> a <> nothing -> b <> nothing ->
    base_type_is_subtype_of env a b = true -> base_type_is_subtype_of env b c = true ->
    length xs = length (parameter_ids a) -> (forall x, In x xs -> argument_in_fragment x = true) ->
    parameterized_supertype_arguments env a xs c
    = parameterized_supertype_arguments env b (parameterized_supertype_arguments env a xs b) c.
Proof.
    intros a b c xs Hab Hbc Hac Ha Hb Hsab Hsbc Hl Hxs.
    rewrite !parameterized_supertype_arguments_eq, (supertypes_compose a b c Hab Hbc Hac Ha Hb Hsab Hsbc), map_map.
    destruct (supertypes_are_templates a b Hab Ha Hsab) as [Hlab Htab].
    destruct (supertypes_are_templates b c Hbc Hb Hsbc) as [_ Htbc].
    apply map_ext_in. intros t Ht. symmetry.
    exact (proj2 (proj2 (compose_with_arguments a b xs (supertype_arguments a b) Hl Hxs Hlab Htab _) t (le_n _) (Htbc t Ht))).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Within the fragment, unify keeps the variable states                                            *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma arguments_keep_states: forall n targs aargs s u,
    (forall t a s0 u0, In t targs -> In a aargs -> unify env n t a (Ongoing s0) = Some (Ongoing u0) -> u0 = s0) ->
    unify_arguments (unify env n) targs aargs s = Some (Ongoing u) -> u = s.
Proof.
    intros n targs. induction targs as [|t targs IH]; intros [|a aargs] s u Hk H; unfold unify_arguments in H; simpl in H;
        try (injection H as ->; reflexivity).
    destruct (unify env n t a (Ongoing s)) as [[w|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
    pose proof (Hk t a s w (or_introl eq_refl) (or_introl eq_refl) E). subst w.
    apply (IH aargs s u); [|exact H]. intros t' a' s0 u0 Ht' Ha'. apply Hk; right; assumption.
Qed.

Lemma keeps_states_with_arguments: forall n,
    (forall t a s u, in_fragment t = true -> in_fragment a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s)
    /\ (forall t a s u, argument_in_fragment t = true -> argument_in_fragment a = true ->
        unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s).
Proof.
    induction n as [|n [IHt IHa]]; [split; intros t a s u _ _ H; discriminate H|].
    split.
    - intros t a s u Ht Ha H.
      destruct (fragment_cases t Ht) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> Ht']]]]];
          destruct (fragment_cases a Ha) as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> Ha']]]]].
      + destruct (root_in_fragment _ _ _ Ht) as [_ Htargs].
        destruct (root_in_fragment _ _ _ Ha) as [Hla Haargs].
        rewrite unify_classes in H.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (class_eqb ca nothing) eqn:Hcn; [injection H as ->; reflexivity|].
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        * rewrite class_eqb_refl in H. apply (arguments_keep_states n targs aargs s u); [|exact H].
          intros t' a' s0 u0 Ht' Ha'. apply IHa; auto.
        * rewrite (class_eqb_false _ _ Hne) in H.
          destruct (supertype_arguments_in_fragment ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hla Haargs)
              as [_ Hnorm].
          apply (arguments_keep_states n targs (parameterized_supertype_arguments env ca aargs ct) s u); [|exact H].
          intros t' a' s0 u0 Ht' Ha'. apply IHa; auto.
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_class in H. exact (IHt _ _ s u Ht' Ha H).
      + rewrite unify_nullable_nullable in H. exact (IHt _ _ s u Ht' Ha' H).
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] s u Ht Ha H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      rewrite unify_type_arguments in H. destruct (ownership_is_assignable_to oa ot); [|discriminate H].
      destruct vt, va; unfold compare_variances in H; try discriminate H;
          try exact (IHt _ _ s u Ht Ha H); try exact (IHt _ _ s u Ha Ht H);
          try exact (IHt _ _ s u Ht top_in_fragment H); try exact (IHt _ _ s u bottom_in_fragment Ht H).
      destruct (unify env n nt na (Ongoing s)) as [[w|]|] eqn:E; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
      pose proof (IHt _ _ s w Ht Ha E). subst w. exact (IHt _ _ s u Ha Ht H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Replacing type arguments                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* The pairs of type arguments of a unification that succeeds *)
Lemma pairwise_of_arguments: forall n targs aargs s,
    length targs = length aargs ->
    (forall t a w, In t targs -> In a aargs -> unify env n t a (Ongoing s) = Some (Ongoing w) -> w = s) ->
    unify_arguments (unify env n) targs aargs s = Some (Ongoing s) ->
    Forall2 (fun a t => unify env n t a (Ongoing s) = Some (Ongoing s)) aargs targs.
Proof.
    intros n targs. induction targs as [|t targs IH]; intros [|a aargs] s Hl Hk H; simpl in Hl; try discriminate Hl;
        [constructor|].
    unfold unify_arguments in H. simpl in H.
    destruct (unify env n t a (Ongoing s)) as [[w|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
    pose proof (Hk t a w (or_introl eq_refl) (or_introl eq_refl) E). subst w.
    constructor; [exact E|]. apply IH; [lia| |exact H]. intros t' a' w Ht Ha. apply Hk; right; assumption.
Qed.

(* Where each assignee xs takes the place of an assignee ys, in what the targets zs are unified with *)
Lemma arguments_forward: forall n2 n3 (zs_all xs ys: list EType) s,
    Forall2 (fun x y => forall z, In z zs_all ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) -> unify env n3 z x (Ongoing s) = Some (Ongoing s)) xs ys ->
    forall zs, incl zs zs_all ->
    (forall y z w, In y ys -> In z zs -> unify env n2 z y (Ongoing s) = Some (Ongoing w) -> w = s) ->
    unify_arguments (unify env n2) zs ys s = Some (Ongoing s) ->
    unify_arguments (unify env n3) zs xs s = Some (Ongoing s).
Proof.
    intros n2 n3 zs_all xs ys s H. induction H as [|x y xs ys Hxy H IH]; intros [|z zs] Hincl Hk H2;
        try reflexivity.
    unfold unify_arguments in *. simpl in H2 |- *.
    destruct (unify env n2 z y (Ongoing s)) as [[w|]|] eqn:E; [|rewrite fold_stays_failed in H2; discriminate H2|discriminate H2].
    pose proof (Hk y z w (or_introl eq_refl) (or_introl eq_refl) E). subst w.
    rewrite (Hxy z (Hincl z (or_introl eq_refl)) E).
    apply (IH zs); [|intros y' z' w Hy Hz; apply Hk; right; assumption|exact H2].
    intros z' Hz. apply Hincl. right. exact Hz.
Qed.

(* The same, for targets *)
Lemma arguments_backward: forall n2 n3 (zs_all xs ys: list EType) s,
    Forall2 (fun x y => forall z, In z zs_all ->
        unify env n2 y z (Ongoing s) = Some (Ongoing s) -> unify env n3 x z (Ongoing s) = Some (Ongoing s)) xs ys ->
    forall zs, incl zs zs_all ->
    (forall y z w, In y ys -> In z zs -> unify env n2 y z (Ongoing s) = Some (Ongoing w) -> w = s) ->
    unify_arguments (unify env n2) ys zs s = Some (Ongoing s) ->
    unify_arguments (unify env n3) xs zs s = Some (Ongoing s).
Proof.
    intros n2 n3 zs_all xs ys s H. induction H as [|x y xs ys Hxy H IH]; intros [|z zs] Hincl Hk H2;
        try reflexivity.
    unfold unify_arguments in *. simpl in H2 |- *.
    destruct (unify env n2 y z (Ongoing s)) as [[w|]|] eqn:E; [|rewrite fold_stays_failed in H2; discriminate H2|discriminate H2].
    pose proof (Hk y z w (or_introl eq_refl) (or_introl eq_refl) E). subst w.
    rewrite (Hxy z (Hincl z (or_introl eq_refl)) E).
    apply (IH zs); [|intros y' z' w Hy Hz; apply Hk; right; assumption|exact H2].
    intros z' Hz. apply Hincl. right. exact Hz.
Qed.

(* The assignee of a comparison of variances replaced: it takes being able to replace it as an
   assignee, where the target variance is out or invariant, and as a target, where it is in or
   invariant *)
Lemma compare_variances_assignee: forall (u u': UnifyFn) vt va t a a' s,
    (forall x y, u x y Failed = Some Failed) ->
    (forall w, u t a (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (u t a (Ongoing s) = Some (Ongoing s) -> u' t a' (Ongoing s) = Some (Ongoing s)) ->
    (u a t (Ongoing s) = Some (Ongoing s) -> u' a' t (Ongoing s) = Some (Ongoing s)) ->
    (u t top_type (Ongoing s) = Some (Ongoing s) -> u' t top_type (Ongoing s) = Some (Ongoing s)) ->
    (u bottom_type t (Ongoing s) = Some (Ongoing s) -> u' bottom_type t (Ongoing s) = Some (Ongoing s)) ->
    compare_variances u vt va t a s = Some (Ongoing s) -> compare_variances u' vt va t a' s = Some (Ongoing s).
Proof.
    intros u u' vt va t a a' s Hf Hk Hfw Hbw Htop Hbot H. destruct vt, va; unfold compare_variances in *; try discriminate H; auto.
    apply both_ways in H; [|exact Hf|exact Hk]. destruct H as [H1 H2]. rewrite (Hfw H1). exact (Hbw H2).
Qed.

Lemma compare_variances_target: forall (u u': UnifyFn) vt va t t' a s,
    (forall x y, u x y Failed = Some Failed) ->
    (forall w, u t a (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (u t a (Ongoing s) = Some (Ongoing s) -> u' t' a (Ongoing s) = Some (Ongoing s)) ->
    (u a t (Ongoing s) = Some (Ongoing s) -> u' a t' (Ongoing s) = Some (Ongoing s)) ->
    (u t top_type (Ongoing s) = Some (Ongoing s) -> u' t' top_type (Ongoing s) = Some (Ongoing s)) ->
    (u bottom_type t (Ongoing s) = Some (Ongoing s) -> u' bottom_type t' (Ongoing s) = Some (Ongoing s)) ->
    compare_variances u vt va t a s = Some (Ongoing s) -> compare_variances u' vt va t' a s = Some (Ongoing s).
Proof.
    intros u u' vt va t t' a s Hf Hk Hfw Hbw Htop Hbot H. destruct vt, va; unfold compare_variances in *; try discriminate H; auto.
    apply both_ways in H; [|exact Hf|exact Hk]. destruct H as [H1 H2]. rewrite (Hfw H1). exact (Hbw H2).
Qed.

(* Below `exclusive Nothing` is nothing but itself, which is below everything *)
Lemma below_bottom: forall n z s, in_fragment z = true ->
    unify env n bottom_type z (Ongoing s) = Some (Ongoing s) ->
    forall t f, in_fragment t = true -> 2 <= f -> unify env f t z (Ongoing s) = Some (Ongoing s).
Proof.
    intros [|n] z s Hz H t f Ht Hf; [discriminate H|].
    destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> _]]]]];
        [|unfold bottom_type in H; rewrite unify_class_nullable in H; discriminate H].
    unfold bottom_type in H. rewrite unify_classes in H.
    destruct (base_type_is_subtype_of env cz nothing) eqn:Hb; [|discriminate H].
    apply only_nothing_is_below_nothing in Hb. subst cz.
    assert (Hmz: mutability_of env (RootResolved mz nothing zargs) = exclusive).
    { destruct (Model.is_subtype_of (mutability_of env (RootResolved mz nothing zargs))
          (mutability_of env (RootResolved (Some exclusive) nothing []))) eqn:Hm; [|discriminate H].
      cbn [mutability_of] in Hm |- *. rewrite nothing_is_no_scalar in Hm |- *.
      destruct mz as [[]|]; simpl in Hm |- *; congruence. }
    assert (Hclass: forall f' mt ct targs, 1 <= f' ->
        unify env f' (RootResolved mt ct targs) (RootResolved mz nothing zargs) (Ongoing s) = Some (Ongoing s)).
    { intros [|f'] mt ct targs Hf'; [lia|]. rewrite unify_classes, nothing_is_below_all, Hmz, class_eqb_refl. reflexivity. }
    destruct (fragment_cases t Ht) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]].
    - apply Hclass. lia.
    - destruct f as [|f]; [lia|]. rewrite unify_nullable_class. apply Hclass. lia.
Qed.

(* Above `read Any?` is nothing but `read Any?` itself, which is above everything *)
Lemma above_top: forall n z s, in_fragment z = true ->
    unify env n z top_type (Ongoing s) = Some (Ongoing s) ->
    forall t f, in_fragment t = true -> 2 <= f -> unify env f z t (Ongoing s) = Some (Ongoing s).
Proof.
    intros [|n] z s Hz H t f Ht Hf; [discriminate H|].
    destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
        [unfold top_type in H; rewrite unify_class_nullable in H; discriminate H|].
    unfold top_type in H. rewrite unify_nullable_nullable in H.
    destruct n as [|n]; [discriminate H|]. rewrite unify_classes in H.
    destruct (base_type_is_subtype_of env any cz) eqn:Hb; [|discriminate H].
    assert (Hcz: cz = any).
    { apply base_type_is_subtype_of_iff in Hb. destruct Hb as [Hb|[Hb|[_ [Hb|Hb]]]]; auto; [discriminate Hb|].
      rewrite any_has_no_supertypes in Hb. contradiction. }
    subst cz.
    destruct (root_in_fragment _ _ _ Hz') as [Hlz _]. rewrite any_has_no_type_parameters in Hlz.
    destruct zargs; [|discriminate Hlz].
    destruct (Model.is_subtype_of (mutability_of env (RootResolved (Some readonly) any []))
        (mutability_of env (RootResolved mz any []))) eqn:Hm; [|discriminate H].
    assert (Hmz: forall a, Model.is_subtype_of a (mutability_of env (RootResolved mz any [])) = true).
    { cbn [mutability_of] in Hm |- *. rewrite any_is_no_scalar in Hm |- *.
      destruct mz as [[]|]; simpl in Hm |- *; try discriminate Hm; intros []; reflexivity. }
    assert (Hclass: forall f' mt ct targs, 1 <= f' ->
        unify env f' (RootResolved mz any []) (RootResolved mt ct targs) (Ongoing s) = Some (Ongoing s)).
    { intros [|f'] mt ct targs Hf'; [lia|]. rewrite unify_classes, Hmz.
      replace (base_type_is_subtype_of env ct any) with true
          by (symmetry; apply base_type_is_subtype_of_iff; auto).
      destruct (class_eqb ct nothing); [reflexivity|].
      destruct (class_eqb ct any); reflexivity. }
    destruct f as [|f]; [lia|].
    destruct (fragment_cases t Ht) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]].
    - rewrite unify_nullable_class. apply Hclass. lia.
    - rewrite unify_nullable_nullable. apply Hclass. lia.
Qed.

(* A type argument that isn't loose stands in for nothing but its equals *)
Lemma exact_symmetric: forall f x y s, argument_in_fragment x = true -> argument_in_fragment y = true ->
    unify env f y x (Ongoing s) = Some (Ongoing s) -> is_loose y = false -> unify env f x y (Ongoing s) = Some (Ongoing s).
Proof.
    intros [|f] [| | | |vx ox X| |] [| | | |vy oy Y| |] s Hx Hy H Hl; simpl in Hx, Hy; try discriminate.
    rewrite unify_type_arguments in H |- *.
    destruct vy; simpl in Hl; try discriminate Hl.
    destruct (ownership_is_assignable_to ox oy) eqn:Ho; [|discriminate H].
    destruct vx; unfold compare_variances in H |- *; try discriminate H.
    assert (Hoo: ox = oy).
    { destruct ox as [| | |p], oy as [| | |q]; simpl in Hl, Ho; try discriminate; try reflexivity.
      apply param_eqb_eq in Ho. congruence. }
    subst oy. rewrite ownership_is_assignable_to_itself.
    apply both_ways in H; [|apply unify_keeps_failure|intros w; apply (proj1 (keeps_states_with_arguments f)); assumption].
    destruct H as [H1 H2]. rewrite H2. exact H1.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Lifting: instantiated templates, compared                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* x can stand in for y as an assignee, at a cost of C fuel, wherever y can with fuel up to m *)
Definition lifts (frag: EType -> bool) (m C: nat) (s: VariableStates) (x y: EType): Prop :=
    forall z m', m' <= m -> frag z = true ->
        unify env m' z y (Ongoing s) = Some (Ongoing s) -> unify env (m' + C) z x (Ongoing s) = Some (Ongoing s).

(* ... and as a target *)
Definition lifts_back (frag: EType -> bool) (m C: nat) (s: VariableStates) (x y: EType): Prop :=
    forall z m', m' <= m -> frag z = true ->
        unify env m' y z (Ongoing s) = Some (Ongoing s) -> unify env (m' + C) x z (Ongoing s) = Some (Ongoing s).

(* Each type argument xs can stand in for the corresponding one of ys as an assignee; as a target, too,
   where that one isn't loose, and then neither is it *)
Definition leaves_lift (m C: nat) (s: VariableStates) (xs ys: list EType): Prop :=
    Forall2 (fun x y => lifts argument_in_fragment m C s x y
        /\ (is_loose y = false -> is_loose x = false /\ lifts_back argument_in_fragment m C s x y)) xs ys.

Lemma leaves_lift_weaken: forall m C s xs ys, leaves_lift (S m) C s xs ys -> leaves_lift m C s xs ys.
Proof.
    intros m C s xs ys H. eapply Forall2_impl; [|exact H]. intros x y [Hf Hb]. split.
    - intros z m' Hm. apply Hf. lia.
    - intros Hl. destruct (Hb Hl) as [Hx Hback]. split; [exact Hx|]. intros z m' Hm. apply Hback. lia.
Qed.

Lemma mentions_arguments_false: forall b arguments,
    existsb (mentions_loosely_bound b) arguments = false -> forall a, In a arguments -> mentions_loosely_bound b a = false.
Proof.
    intros b arguments H a Ha. destruct (mentions_loosely_bound b a) eqn:E; [|reflexivity].
    assert (existsb (mentions_loosely_bound b) arguments = true) by (apply existsb_exists; eauto). congruence.
Qed.

(* Where the type arguments xs of one reference to `sub` can stand in for those ys of another, the
   templates of `sub`, instantiated with xs, can stand in for those instantiated with ys; as targets
   too, where they aren't widened *)
Lemma lifting: forall C s, 1 <= C -> forall m sub xs ys,
    length xs = length (parameter_ids sub) -> length ys = length (parameter_ids sub) ->
    (forall x, In x xs -> argument_in_fragment x = true) -> (forall y, In y ys -> argument_in_fragment y = true) ->
    leaves_lift m C s xs ys ->
    (forall t, template_type sub t = true ->
        lifts in_fragment m C s (instantiate env (bindings_of env sub xs) t) (instantiate env (bindings_of env sub ys) t)
        /\ (mentions_loosely_bound (bindings_of env sub ys) t = false ->
            lifts_back in_fragment m C s (instantiate env (bindings_of env sub xs) t) (instantiate env (bindings_of env sub ys) t)))
    /\ (forall a, template_argument sub a = true ->
        lifts argument_in_fragment m C s (instantiate env (bindings_of env sub xs) a) (instantiate env (bindings_of env sub ys) a)
        /\ (mentions_loosely_bound (bindings_of env sub ys) a = false ->
            lifts_back argument_in_fragment m C s (instantiate env (bindings_of env sub xs) a) (instantiate env (bindings_of env sub ys) a))).
Proof.
    intros C s HC m. induction m as [|m IH]; intros sub xs ys Hlx Hly Hxs Hys HL.
    { assert (H0: forall frag x y, lifts frag 0 C s x y /\ lifts_back frag 0 C s x y).
      { intros frag x y. split; intros z m' Hm' _ H; assert (m' = 0) by lia; subst m'; discriminate H. }
      split; intros t _; (split; [apply H0|intros _; apply H0]). }
    destruct (IH sub xs ys Hlx Hly Hxs Hys (leaves_lift_weaken _ _ _ _ _ HL)) as [IHt IHa].
    assert (Hloose: Forall2 (fun x y => is_loose x = true -> is_loose y = true) xs ys).
    { eapply Forall2_impl; [|exact HL]. intros x y [_ Hb] Hx. destruct (is_loose y) eqn:E; [reflexivity|].
      destruct (Hb eq_refl) as [Hx' _]. congruence. }
    pose proof (mentions_monotone_with_arguments sub xs ys Hlx Hly Hloose) as Hmono.
    assert (Hxs': forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply argument_in_fragment_is_type_argument, Hxs, Hx).
    assert (Hys': forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; apply argument_in_fragment_is_type_argument, Hys, Hy).
    (* the type arguments of a class type of a template, instantiated, and those of a supertype *)
    assert (Hinst_args: forall targs, (forall u, In u targs -> template_argument sub u = true) ->
        (forall a, In a (map (instantiate env (bindings_of env sub xs)) targs) -> argument_in_fragment a = true)
        /\ (forall a, In a (map (instantiate env (bindings_of env sub ys)) targs) -> argument_in_fragment a = true)).
    { intros targs Htargs. split; intros a Ha; apply in_map_iff in Ha; destruct Ha as [u [<- Hu]];
          apply template_instance_in_fragment; auto. }
    assert (Hclass: forall m0 c targs, template_type sub (RootResolved m0 c targs) = true ->
        lifts in_fragment (S m) C s
            (RootResolved m0 c (map (instantiate env (bindings_of env sub xs)) targs))
            (RootResolved m0 c (map (instantiate env (bindings_of env sub ys)) targs))
        /\ (mentions_loosely_bound (bindings_of env sub ys) (RootResolved m0 c targs) = false ->
            lifts_back in_fragment (S m) C s
                (RootResolved m0 c (map (instantiate env (bindings_of env sub xs)) targs))
                (RootResolved m0 c (map (instantiate env (bindings_of env sub ys)) targs)))).
    { intros m0 c targs Ht. destruct (root_template sub m0 c targs Ht) as [Hlt Htargs].
      destruct (Hinst_args targs Htargs) as [Hfx Hfy].
      pose proof (proj1 (IHt _ Ht)) as IHself. rewrite !instantiate_class in IHself.
      split.
      - intros z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
        destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]].
        + destruct (root_in_fragment mz cz zargs Hz) as [_ Hzargs].
          rewrite unify_classes in H |- *.
          rewrite (mutability_of_class m0 c (map (instantiate env (bindings_of env sub xs)) targs)
              (map (instantiate env (bindings_of env sub ys)) targs)).
          destruct (base_type_is_subtype_of env c cz) eqn:Hb; [|discriminate H].
          destruct (Model.is_subtype_of _ _); [|discriminate H].
          destruct (class_eqb c nothing) eqn:Hcn; [reflexivity|].
          destruct (Class_eq_dec c cz) as [<-|Hne].
          * rewrite class_eqb_refl in H |- *.
            apply (arguments_forward m'' (m'' + C) zargs _ (map (instantiate env (bindings_of env sub ys)) targs) s);
                [|apply incl_refl| |exact H].
            -- apply Forall2_map_same. intros u Hu z' Hz' E.
               apply (proj1 (IHa u (Htargs u Hu))); [lia|apply Hzargs, Hz'|exact E].
            -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments m'') z' y' s w); auto.
          * rewrite (class_eqb_false _ _ Hne) in H |- *. rewrite !parameterized_supertype_arguments_eq in H |- *.
            assert (Hcn': c <> nothing) by (apply class_eqb_false_neq; exact Hcn).
            destruct (supertypes_are_templates c cz Hne Hcn' Hb) as [_ Hst].
            assert (Hleaves: leaves_lift m C s
                (map (instantiate env (bindings_of env sub xs)) targs) (map (instantiate env (bindings_of env sub ys)) targs)).
            { apply Forall2_map_same. intros u Hu. split; [exact (proj1 (IHa u (Htargs u Hu)))|].
              intros Hly'. rewrite (loose_instance sub ys u Hly Hys' (Htargs u Hu)) in Hly'.
              apply orb_false_iff in Hly'. destruct Hly' as [Hlu Hmu]. split.
              - rewrite (loose_instance sub xs u Hlx Hxs' (Htargs u Hu)), Hlu.
                destruct (mentions_loosely_bound (bindings_of env sub xs) u) eqn:E; [|reflexivity].
                pose proof (argument_depth_below m0 c targs u Hu).
                rewrite (proj2 (Hmono _) u (le_n _) (Htargs u Hu) E) in Hmu. discriminate Hmu.
              - exact (proj2 (IHa u (Htargs u Hu)) Hmu). }
            assert (Hl': length (map (instantiate env (bindings_of env sub xs)) targs) = length (parameter_ids c))
                by (rewrite length_map; exact Hlt).
            assert (Hl'': length (map (instantiate env (bindings_of env sub ys)) targs) = length (parameter_ids c))
                by (rewrite length_map; exact Hlt).
            destruct (IH c _ _ Hl' Hl'' Hfx Hfy Hleaves) as [_ IHc].
            apply (arguments_forward m'' (m'' + C) zargs _
                (map (instantiate env (bindings_of env c (map (instantiate env (bindings_of env sub ys)) targs)))
                    (supertype_arguments c cz)) s); [|apply incl_refl| |exact H].
            -- apply Forall2_map_same. intros r Hr z' Hz' E.
               apply (proj1 (IHc r (Hst r Hr))); [lia|apply Hzargs, Hz'|exact E].
            -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments m'') z' y' s w); auto.
               apply in_map_iff in Hy'. destruct Hy' as [r [<- Hr]]. apply template_instance_in_fragment; auto.
        + rewrite unify_nullable_class in H |- *. apply IHself; [lia|exact Hz'|exact H].
      - intros Hm z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
        rewrite mentions_class in Hm. pose proof (mentions_arguments_false _ targs Hm) as Hmu.
        destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
            [|rewrite unify_class_nullable in H; discriminate H].
        destruct (root_in_fragment mz cz zargs Hz) as [Hlz Hzargs].
        rewrite unify_classes in H |- *.
        rewrite (mutability_of_class m0 c (map (instantiate env (bindings_of env sub xs)) targs)
            (map (instantiate env (bindings_of env sub ys)) targs)).
        destruct (base_type_is_subtype_of env cz c) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (class_eqb cz nothing) eqn:Hcn; [reflexivity|].
        destruct (Class_eq_dec cz c) as [->|Hne].
        * rewrite class_eqb_refl in H |- *.
          apply (arguments_backward m'' (m'' + C) zargs _ (map (instantiate env (bindings_of env sub ys)) targs) s);
              [|apply incl_refl| |exact H].
          -- apply Forall2_map_same. intros u Hu z' Hz' E.
             apply (proj2 (IHa u (Htargs u Hu)) (Hmu u Hu)); [lia|apply Hzargs, Hz'|exact E].
          -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments m'') y' z' s w); auto.
        * rewrite (class_eqb_false _ _ Hne) in H |- *.
          destruct (supertype_arguments_in_fragment cz c zargs Hne (class_eqb_false_neq _ _ Hcn) Hb Hlz Hzargs)
              as [_ Hnorm].
          apply (arguments_backward m'' (m'' + C) (parameterized_supertype_arguments env cz zargs c) _
              (map (instantiate env (bindings_of env sub ys)) targs) s); [|apply incl_refl| |exact H].
          -- apply Forall2_map_same. intros u Hu z' Hz' E.
             apply (proj2 (IHa u (Htargs u Hu)) (Hmu u Hu)); [lia|apply Hnorm, Hz'|exact E].
          -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments m'') y' z' s w); auto. }
    split.
    - intros t Ht. destruct (template_type_cases sub t Ht) as [[m0 [c [targs ->]]]|[m0 [c [targs [-> Ht']]]]].
      + rewrite !instantiate_class. exact (Hclass m0 c targs Ht).
      + rewrite !instantiate_nullable_class, mentions_nullable.
        destruct (Hclass m0 c targs Ht') as [Hf Hb]. split.
        * intros z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
          destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
              [rewrite unify_class_nullable in H; discriminate H|].
          rewrite unify_nullable_nullable in H |- *. apply Hf; [lia|exact Hz'|exact H].
        * intros Hm z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
          destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]].
          -- rewrite unify_nullable_class in H |- *. apply (Hb Hm); [lia|exact Hz|exact H].
          -- rewrite unify_nullable_nullable in H |- *. apply (Hb Hm); [lia|exact Hz'|exact H].
    - intros a Ha. destruct (template_kind sub a Ha) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ xs i p (eq_sym Hlx) Hi) as [x Hx].
        destruct (nth_error_same_length _ ys i p (eq_sym Hly) Hi) as [y Hy].
        rewrite (selects sub xs p bp i x Hi Hx (Hxs' x (nth_error_In _ _ Hx))).
        rewrite (selects sub ys p bp i y Hi Hy (Hys' y (nth_error_In _ _ Hy))).
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter sub ys i p y Hi Hy)).
        destruct (Forall2_nth_error _ xs ys i x y HL Hx Hy) as [Hf Hb]. split; [exact Hf|].
        intros Hl. exact (proj2 (Hb Hl)).
      + destruct (IHt n Hn) as [IHn_f IHn_b].
        pose proof (template_shape sub n Hn) as Hshape.
        pose proof (template_type_instance_in_fragment sub xs n Hlx Hxs Hn) as Hfx.
        pose proof (template_type_instance_in_fragment sub ys n Hly Hys Hn) as Hfy.
        change (mentions_loosely_bound (bindings_of env sub ys) (TypeArgument v o n))
            with (mentions_loosely_bound (bindings_of env sub ys) n).
        rewrite (instantiate_template_argument (bindings_of env sub xs) v o n Ho Hshape).
        rewrite (instantiate_template_argument (bindings_of env sub ys) v o n Ho Hshape).
        destruct (mentions_loosely_bound (bindings_of env sub ys) n) eqn:Ey;
            destruct (mentions_loosely_bound (bindings_of env sub xs) n) eqn:Ex.
        * (* both widened *)
          split; [|intros Hm; discriminate Hm].
          intros z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
          destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
          destruct v; cbn beta iota in H |- *;
              rewrite unify_type_arguments in H |- *; destruct (ownership_is_assignable_to o oz); try discriminate H;
              destruct vz; unfold compare_variances in H |- *; try discriminate H;
              first [ apply IHn_f; [lia|exact Hz|exact H]
                    | apply (unify_fuel_monotone env m''); [lia|exact H] ].
        * (* widened for ys only *)
          split; [|intros Hm; discriminate Hm].
          intros z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
          destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
          destruct v; cbn beta iota in H |- *;
              rewrite unify_type_arguments in H |- *; destruct (ownership_is_assignable_to o oz); try discriminate H;
              destruct vz; unfold compare_variances in H |- *; try discriminate H;
              first [ apply IHn_f; [lia|exact Hz|exact H]
                    | apply (unify_fuel_monotone env m''); [lia|exact H]
                    (* widened to `out` or `in Nothing`: what takes no more than Nothing, a Box<X> takes, too *)
                    | destruct m'' as [|m'']; [discriminate H|];
                      apply (below_bottom (S m'') Z s Hz H _ _ Hfx); lia ].
        * (* widened for xs only: can't be *)
          exfalso. rewrite (proj1 (Hmono _) n (le_n _) Hn Ex) in Ey. discriminate Ey.
        * (* widened for neither *)
          split.
          -- intros z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
             destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
             rewrite unify_type_arguments in H |- *. destruct (ownership_is_assignable_to o oz); [|discriminate H].
             apply (compare_variances_assignee (unify env m'') (unify env (m'' + C)) vz v Z
                 (instantiate env (bindings_of env sub ys) n) (instantiate env (bindings_of env sub xs) n) s);
                 [apply unify_keeps_failure| | | | | |exact H].
             ++ intros w. apply (proj1 (keeps_states_with_arguments m'')); [exact Hz|exact Hfy].
             ++ intros E. apply IHn_f; [lia|exact Hz|exact E].
             ++ intros E. apply (IHn_b eq_refl); [lia|exact Hz|exact E].
             ++ intros E. apply (unify_fuel_monotone env m''); [lia|exact E].
             ++ intros E. apply (unify_fuel_monotone env m''); [lia|exact E].
          -- intros _ z m' Hm' Hz H. destruct m' as [|m'']; [discriminate H|]. change (S m'' + C) with (S (m'' + C)).
             destruct z as [| | | |vz oz Z| |]; simpl in Hz; try discriminate Hz.
             rewrite unify_type_arguments in H |- *. destruct (ownership_is_assignable_to oz o); [|discriminate H].
             apply (compare_variances_target (unify env m'') (unify env (m'' + C)) v vz
                 (instantiate env (bindings_of env sub ys) n) (instantiate env (bindings_of env sub xs) n) Z s);
                 [apply unify_keeps_failure| | | | | |exact H].
             ++ intros w. apply (proj1 (keeps_states_with_arguments m'')); [exact Hfy|exact Hz].
             ++ intros E. apply (IHn_b eq_refl); [lia|exact Hz|exact E].
             ++ intros E. apply IHn_f; [lia|exact Hz|exact E].
             ++ intros E. apply (IHn_b eq_refl); [lia|exact top_in_fragment|exact E].
             ++ intros E. apply IHn_f; [lia|exact bottom_in_fragment|exact E].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Transitivity                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma compare_variances_transitive: forall (u1 u2 u3: UnifyFn) v1 v2 v3 x y z s,
    (forall t a, u1 t a Failed = Some Failed) -> (forall t a, u2 t a Failed = Some Failed) ->
    (forall w, u1 y x (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (forall w, u2 z y (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (u1 y x (Ongoing s) = Some (Ongoing s) -> u2 z y (Ongoing s) = Some (Ongoing s) -> u3 z x (Ongoing s) = Some (Ongoing s)) ->
    (u2 y z (Ongoing s) = Some (Ongoing s) -> u1 x y (Ongoing s) = Some (Ongoing s) -> u3 x z (Ongoing s) = Some (Ongoing s)) ->
    (* the same, with `read Any?` and `exclusive Nothing` in place of x *)
    (u1 y top_type (Ongoing s) = Some (Ongoing s) -> u2 z y (Ongoing s) = Some (Ongoing s) -> u3 z top_type (Ongoing s) = Some (Ongoing s)) ->
    (u2 y z (Ongoing s) = Some (Ongoing s) -> u1 bottom_type y (Ongoing s) = Some (Ongoing s) -> u3 bottom_type z (Ongoing s) = Some (Ongoing s)) ->
    (u2 z top_type (Ongoing s) = Some (Ongoing s) -> u3 z top_type (Ongoing s) = Some (Ongoing s)) ->
    (u2 bottom_type z (Ongoing s) = Some (Ongoing s) -> u3 bottom_type z (Ongoing s) = Some (Ongoing s)) ->
    (* what takes `read Any?` takes x, and what `exclusive Nothing` takes, x takes *)
    (u2 z top_type (Ongoing s) = Some (Ongoing s) -> u3 z x (Ongoing s) = Some (Ongoing s)) ->
    (u2 bottom_type z (Ongoing s) = Some (Ongoing s) -> u3 x z (Ongoing s) = Some (Ongoing s)) ->
    compare_variances u1 v2 v1 y x s = Some (Ongoing s) ->
    compare_variances u2 v3 v2 z y s = Some (Ongoing s) ->
    compare_variances u3 v3 v1 z x s = Some (Ongoing s).
Proof.
    intros u1 u2 u3 v1 v2 v3 x y z s Hf1 Hf2 Hk1 Hk2 Hforward Hbackward Hforward_top Hbackward_bottom
        Hmono_top Hmono_bottom Habove Hbelow H1 H2.
    destruct v1, v2, v3; unfold compare_variances in *; try discriminate H1; try discriminate H2;
        repeat match goal with
        | H: match u1 _ _ (Ongoing s) with Some _ => _ | None => None end = Some (Ongoing s) |- _ =>
            apply both_ways in H; [destruct H|exact Hf1|exact Hk1]
        | H: match u2 _ _ (Ongoing s) with Some _ => _ | None => None end = Some (Ongoing s) |- _ =>
            apply both_ways in H; [destruct H|exact Hf2|exact Hk2]
        end;
        first [rewrite Hforward by assumption; apply Hbackward; assumption | apply Hforward; assumption | apply Hbackward; assumption
              | apply Hforward_top; assumption | apply Hbackward_bottom; assumption
              | apply Hmono_top; assumption | apply Hmono_bottom; assumption
              | apply Habove; assumption | apply Hbelow; assumption].
Qed.

(* By induction on the fuel the two assignments take together: the type arguments compared may come
   from instantiated supertypes, which aren't part of the types compared *)
Lemma transitivity_with_arguments: forall N,
    (forall x y z n1 n2 s, n1 + n2 <= N ->
        in_fragment x = true -> in_fragment y = true -> in_fragment z = true ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s))
    /\ (forall x y z n1 n2 s, n1 + n2 <= N ->
        argument_in_fragment x = true -> argument_in_fragment y = true -> argument_in_fragment z = true ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s)).
Proof.
    induction N as [|N [IHt IHa]].
    { split; intros x y z n1 n2 s HN _ _ _ H1 _; assert (n1 = 0) by lia; subst n1; discriminate H1. }
    split.
    - intros x y z n1 n2 s HN Hx Hy Hz H1 H2.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      change (S n1' + S n2') with (S (n1' + S n2')).
      destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
          destruct (fragment_cases y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> Hy']]]]];
          destruct (fragment_cases x Hx) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> Hx']]]]];
          try (rewrite unify_class_nullable in H1; discriminate H1);
          try (rewrite unify_class_nullable in H2; discriminate H2).
      + (* three class types *)
        destruct (root_in_fragment _ _ _ Hx) as [Hlx Hxargs].
        destruct (root_in_fragment _ _ _ Hy) as [Hly Hyargs].
        destruct (root_in_fragment _ _ _ Hz) as [Hlz Hzargs].
        rewrite unify_classes in H1, H2 |- *.
        destruct (base_type_is_subtype_of env cx cy) eqn:Hb1; [|discriminate H1].
        destruct (base_type_is_subtype_of env cy cz) eqn:Hb2; [|discriminate H2].
        rewrite (base_type_is_subtype_of_trans cx cy cz Hb1 Hb2).
        destruct (Model.is_subtype_of (mutability_of env (RootResolved mx cx xargs)) (mutability_of env (RootResolved my cy yargs))) eqn:Hm1;
            [|discriminate H1].
        destruct (Model.is_subtype_of (mutability_of env (RootResolved my cy yargs)) (mutability_of env (RootResolved mz cz zargs))) eqn:Hm2;
            [|discriminate H2].
        rewrite (mutability_trans _ _ _ Hm1 Hm2).
        (* Nothing is assignable to every class type *)
        destruct (class_eqb cx nothing) eqn:Hcx; [reflexivity|].
        destruct (class_eqb cy nothing) eqn:Hcy.
        { apply class_eqb_true in Hcy. subst cy. apply only_nothing_is_below_nothing in Hb1. subst cx.
          rewrite class_eqb_refl in Hcx. discriminate Hcx. }
        apply class_eqb_false_neq in Hcx, Hcy.
        (* x, as a reference to the class of y *)
        set (xs1 := if class_eqb cx cy then xargs else parameterized_supertype_arguments env cx xargs cy) in H1.
        assert (Hxs1: length xs1 = length (parameter_ids cy) /\ forall a, In a xs1 -> argument_in_fragment a = true).
        { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy]; [rewrite class_eqb_refl; auto|].
          rewrite (class_eqb_false _ _ Hxy). apply supertype_arguments_in_fragment; assumption. }
        destruct Hxs1 as [Hlxs1 Hfxs1].
        assert (Hpairs: Forall2 (fun a t => unify env n1' t a (Ongoing s) = Some (Ongoing s)) xs1 yargs).
        { apply (pairwise_of_arguments n1' yargs xs1 s); [congruence| |exact H1].
          intros t a w Ht Ha. apply (proj2 (keeps_states_with_arguments n1')); auto. }
        destruct (Class_eq_dec cy cz) as [<-|Hyz].
        * (* y and z are of the same class: x takes the place of y as it is *)
          rewrite class_eqb_refl in H2.
          apply (arguments_forward n2' (n1' + S n2') zargs xs1 yargs s); [|apply incl_refl| |exact H2].
          -- apply (Forall2_impl_in _ _ _ _ Hpairs). intros x' y' Hx' Hy' E1 z' Hz' E2.
             apply (unify_fuel_monotone env (n1' + n2')); [lia|].
             apply (IHa x' y' z' n1' n2' s); auto; lia.
          -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments n2') z' y' s w); auto.
        * (* y is of a subclass of z: lift what x as a reference to the class of y does into the supertype *)
          rewrite (class_eqb_false _ _ Hyz) in H2.
          destruct (Class_eq_dec cx cz) as [<-|Hxz].
          { exfalso. apply Hyz. symmetry. apply acyclic; assumption. }
          rewrite (class_eqb_false _ _ Hxz).
          replace (parameterized_supertype_arguments env cx xargs cz) with (parameterized_supertype_arguments env cy xs1 cz).
          2: { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy]; [rewrite class_eqb_refl; reflexivity|].
               rewrite (class_eqb_false _ _ Hxy). symmetry.
               apply parameterized_supertype_arguments_compose; assumption. }
          destruct (supertype_arguments_in_fragment cy cz yargs Hyz Hcy Hb2 Hly Hyargs) as [_ Hfys].
          destruct (supertypes_are_templates cy cz Hyz Hcy Hb2) as [_ Hst].
          assert (Hleaves: leaves_lift n2' (S n1') s xs1 yargs).
          { apply (Forall2_impl_in _ _ _ _ Hpairs). intros x' y' Hx' Hy' E1. split.
            - intros z' m' Hm' Hz' E2. apply (unify_fuel_monotone env (n1' + m')); [lia|].
              apply (IHa x' y' z' n1' m' s); auto; lia.
            - intros Hl. split.
              + destruct (is_loose x') eqn:E; [|reflexivity].
                rewrite (loose_monotone n1' x' y' s (Hfxs1 x' Hx') (Hyargs y' Hy') E1 E) in Hl. discriminate Hl.
              + intros z' m' Hm' Hz' E2. apply (unify_fuel_monotone env (m' + n1')); [lia|].
                apply (IHa z' y' x' m' n1' s); auto; [lia|].
                apply exact_symmetric; auto. }
          destruct (lifting (S n1') s ltac:(lia) n2' cy xs1 yargs Hlxs1 Hly Hfxs1 Hyargs Hleaves) as [_ Hlift].
          rewrite parameterized_supertype_arguments_eq in H2 |- *.
          replace (n1' + S n2') with (n2' + S n1') by lia.
          apply (arguments_forward n2' (n2' + S n1') zargs _
              (map (instantiate env (bindings_of env cy yargs)) (supertype_arguments cy cz)) s); [|apply incl_refl| |exact H2].
          -- apply Forall2_map_same. intros r Hr z' Hz' E.
             apply (proj1 (Hlift r (Hst r Hr))); [lia|apply Hzargs, Hz'|exact E].
          -- intros y' z' w Hy' Hz' E. apply (proj2 (keeps_states_with_arguments n2') z' y' s w); auto.
             apply Hfys. rewrite parameterized_supertype_arguments_eq. exact Hy'.
      + (* two class types to a nullable type *)
        rewrite unify_nullable_class in H2 |- *.
        replace (n1' + S n2') with (S n1' + n2') by lia.
        apply (IHt (RootResolved mx cx xargs) (RootResolved my cy yargs) (RootResolved mz cz zargs) (S n1') n2' s); [lia|exact Hx|exact Hy|exact Hz'|exact H1|exact H2].
      + (* a class type to a nullable type to a nullable type *)
        rewrite unify_nullable_class in H1 |- *. rewrite unify_nullable_nullable in H2.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt (RootResolved mx cx xargs) (RootResolved my cy yargs) (RootResolved mz cz zargs) n1' n2' s); [lia|exact Hx|exact Hy'|exact Hz'|exact H1|exact H2].
      + (* three nullable types *)
        rewrite unify_nullable_nullable in H1, H2 |- *.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt (RootResolved mx cx xargs) (RootResolved my cy yargs) (RootResolved mz cz zargs) n1' n2' s); [lia|exact Hx'|exact Hy'|exact Hz'|exact H1|exact H2].
    - intros [| | | |v1 o1 x| |] [| | | |v2 o2 y| |] [| | | |v3 o3 z| |] n1 n2 s HN Hx Hy Hz H1 H2;
          simpl in Hx, Hy, Hz; try discriminate Hx; try discriminate Hy; try discriminate Hz.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      change (S n1' + S n2') with (S (n1' + S n2')).
      rewrite unify_type_arguments in H1, H2 |- *.
      destruct (ownership_is_assignable_to o1 o2) eqn:Ho12; [|discriminate H1].
      destruct (ownership_is_assignable_to o2 o3) eqn:Ho23; [|discriminate H2].
      rewrite (ownership_trans o1 o2 o3 Ho12 Ho23).
      apply (compare_variances_transitive (unify env n1') (unify env n2') (unify env (n1' + S n2')) v1 v2 v3 x y z s);
          try assumption.
      + apply unify_keeps_failure.
      + apply unify_keeps_failure.
      + intros w. apply (proj1 (keeps_states_with_arguments n1')); assumption.
      + intros w. apply (proj1 (keeps_states_with_arguments n2')); assumption.
      + intros E1 E2. apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt x y z n1' n2' s); auto; lia.
      + intros E2 E1. apply (unify_fuel_monotone env (n2' + n1')); [lia|].
        apply (IHt z y x n2' n1' s); auto; lia.
      + intros E1 E2. apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt top_type y z n1' n2' s); auto; [lia|exact top_in_fragment].
      + intros E2 E1. apply (unify_fuel_monotone env (n2' + n1')); [lia|].
        apply (IHt z y bottom_type n2' n1' s); auto; [lia|exact bottom_in_fragment].
      + intros E. apply (unify_fuel_monotone env n2'); [lia|exact E].
      + intros E. apply (unify_fuel_monotone env n2'); [lia|exact E].
      + intros E. destruct n2' as [|n2'']; [discriminate E|]. apply (above_top (S n2'') z s Hz E x); [exact Hx|lia].
      + intros E. destruct n2' as [|n2'']; [discriminate E|]. apply (below_bottom (S n2'') z s Hz E x); [exact Hx|lia].
Qed.

(*
 * Transitivity: within the fragment, a type assignable to another, which is assignable to a third,
 * is assignable to the third. The fuel the two assignments take adds up.
 *)
Theorem transitivity: forall n1 n2 x y z,
    in_fragment x = true -> in_fragment y = true -> in_fragment z = true ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    is_assignable_to env (n1 + n2) x z = Some true.
Proof.
    intros n1 n2 x y z Hx Hy Hz H1 H2. unfold is_assignable_to, empty_unification in *.
    destruct (unify env n1 y x (Ongoing [])) as [[u1|]|] eqn:E1; try discriminate H1.
    destruct (unify env n2 z y (Ongoing [])) as [[u2|]|] eqn:E2; try discriminate H2.
    pose proof (proj1 (keeps_states_with_arguments n1) _ _ _ _ Hy Hx E1). subst u1.
    pose proof (proj1 (keeps_states_with_arguments n2) _ _ _ _ Hz Hy E2). subst u2.
    rewrite (proj1 (transitivity_with_arguments (n1 + n2)) x y z n1 n2 [] (le_n _) Hx Hy Hz E1 E2).
    reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Prescribed ownership carries over to supertypes                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Definition prescriptions (c: Class): list (option Ownership) :=
    map prescribed_ownership (type_parameters (declaration_of env c)).

(* A type argument meets the ownership prescribed for its type parameter, if there is one *)
Definition meets (prescription: option Ownership) (a: EType): Prop :=
    forall o, prescription = Some o -> exists v n, a = TypeArgument v o n.

Definition meets_prescriptions (c: Class) (arguments: list EType): Prop := Forall2 meets (prescriptions c) arguments.

Fixpoint prescription_of (parameters: list TypeParameterDecl) (p: TypeParameterId): option Ownership :=
    match parameters with
    | [] => None
    | d :: rest => if param_eqb p (param_id d) then prescribed_ownership d else prescription_of rest p
    end.

(* The rule for the type arguments of supertypes. Where the type parameter of the supertype has a
   prescribed ownership, a type parameter of the subclass in its place must prescribe the same
   (`class A<owned T>`, `class B<owned T> : A<T>`), and any other type argument must have it. Where
   the supertype prescribes none, the subclass may (`class A<T>`, `class B<owned T> : A<T>`). *)
Definition template_meets (sub: Class) (prescription: option Ownership) (t: EType): Prop :=
    match template_parameter t with
    | Some p => forall o, prescription = Some o -> prescription_of (type_parameters (declaration_of env sub)) p = Some o
    | None => meets prescription t
    end.

Hypothesis supertypes_repeat_prescriptions: forall sub super,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    Forall2 (template_meets sub) (prescriptions super) (supertype_arguments sub super).

Lemma prescription_of_nth: forall parameters k p,
    NoDup (map param_id parameters) -> nth_error (map param_id parameters) k = Some p ->
    nth_error (map prescribed_ownership parameters) k = Some (prescription_of parameters p).
Proof.
    intros parameters. induction parameters as [|d rest IH]; intros k p Hnd Hk; [destruct k; discriminate Hk|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. destruct k as [|k]; simpl in Hk |- *.
    - injection Hk as <-. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p (param_id d)) eqn:E.
      + apply param_eqb_eq in E. subst p. exfalso. apply Hnotin. eapply nth_error_In. exact Hk.
      + exact (IH k p Hnd' Hk).
Qed.

(* Type arguments that meet the prescriptions of a class meet those of its supertypes, as
   instantiated with them *)
Theorem prescriptions_carry_over_to_supertypes: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids sub) -> (forall x, In x xs -> argument_in_fragment x = true) ->
    meets_prescriptions sub xs ->
    meets_prescriptions super (parameterized_supertype_arguments env sub xs super).
Proof.
    intros sub super xs Hne Hn Hb Hl Hxs Hm.
    pose proof (supertypes_repeat_prescriptions sub super Hne Hn Hb) as Hrule.
    destruct (supertypes_are_templates sub super Hne Hn Hb) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq. unfold meets_prescriptions.
    remember (prescriptions super) as prs eqn:Hprs. remember (supertype_arguments sub super) as ts eqn:Hts.
    clear Hprs Hts. revert Ht.
    induction Hrule as [|pr t prs ts Hpt Hrule IH]; intros Ht; simpl; constructor.
    - destruct (template_kind sub t (Ht t (or_introl eq_refl))) as [[p [bp [k [-> Hk]]]]|[v [o [n [-> [Hnone [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ xs k p (eq_sym Hl) Hk) as [x Hx].
        rewrite (selects sub xs p bp k x Hk Hx) by (apply argument_in_fragment_is_type_argument, Hxs; eapply nth_error_In; exact Hx).
        assert (Htp: template_parameter (TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))) = Some p)
            by (simpl; unfold param_eqb; rewrite Nat.eqb_refl; reflexivity).
        unfold template_meets in Hpt. rewrite Htp in Hpt.
        intros o Ho. specialize (Hpt o Ho).
        pose proof (prescription_of_nth (type_parameters (declaration_of env sub)) k p (parameter_ids_are_distinct sub) Hk) as Hpk.
        rewrite Hpt in Hpk.
        exact (Forall2_nth_error meets (prescriptions sub) xs k (Some o) x Hm Hpk Hx o eq_refl).
      + unfold template_meets in Hpt. rewrite Hnone in Hpt.
        rewrite (instantiate_template_argument _ v o n Ho (template_shape sub n Hn')).
        intros o' Ho'. destruct (Hpt o' Ho') as [v' [n'' Heq]]. injection Heq as <- <- <-.
        destruct (mentions_loosely_bound _ n); [destruct v|]; eauto.
    - apply IH. intros t' Ht'. apply Ht. right. exact Ht'.
Qed.

End Transitivity.

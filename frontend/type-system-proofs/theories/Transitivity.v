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
(* - class types, never Nothing, with as many type arguments as the class has type parameters;    *)
(*   the type arguments of any variance and ownership;                                             *)
(* - nullable class types;                                                                         *)
(* - without type parameters, type variables, intersections or erroneous types;                   *)
(* and for environments where                                                                      *)
(* - the supertypes are transitive, Any has none, and the class hierarchy has no cycles;          *)
(* - the type parameters of a class are distinct;                                                  *)
(* - the type arguments of supertypes are either a type parameter of the subclass, as it is        *)
(*   (`class B<T> : C<T>`: invariant, of the ownership of T), or don't mention any                  *)
(*   (`class Names : List<owned const String>`); see template_argument;                             *)
(* - the type arguments of a supertype of a supertype are those of the supertype, instantiated     *)
(*   (supertypes_compose).                                                                         *)
(* In that form, instantiating a supertype picks the type arguments of the subtype, so a subtype    *)
(* assignable to another stays so as a supertype, as does the composition of the two. Not covered: *)
(* type parameters nested in the type arguments of supertypes (`class Map<K, V> :                  *)
(* Iterable<Pair<K, V>>`), or with a variance (`class B<T> : C<out T>`).                           *)
(*                                                                                                *)
(* Prescribed ownership (TypeParameterDecl.prescribed_ownership) is carried over to the supertypes,*)
(* if the supertypes repeat it; see prescriptions_carry_over_to_supertypes.                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Transitivity.

Variable env: Environment.

Definition is_class (t: EType): bool :=
    match t with RootResolved _ _ _ => true | _ => false end.

Fixpoint in_fragment (t: EType): bool :=
    match t with
    | RootResolved _ c arguments =>
        negb (class_eqb c nothing)
        && Nat.eqb (length arguments) (length (type_parameters (declaration_of env c)))
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

(* ---------------------------------------------------------------------------------------------- *)
(* The form of supertypes                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Definition parameter_ids (c: Class): list TypeParameterId := map param_id (type_parameters (declaration_of env c)).

Definition is_parameter_ownership (o: Ownership): bool :=
    match o with parameter_ownership _ => true | _ => false end.

(* Whether a type of the fragment mentions no type parameter, not even by ownership *)
Fixpoint concrete (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments =>
        forallb (fun a => match a with TypeArgument _ o n => negb (is_parameter_ownership o) && concrete n | _ => false end) arguments
    | Nullable n => concrete n
    | _ => false
    end.

Definition argument_concrete (a: EType): bool :=
    match a with TypeArgument _ o n => negb (is_parameter_ownership o) && concrete n | _ => false end.

(* The type parameter a type argument is, as it is: `T` *)
Definition template_parameter (t: EType): option TypeParameterId :=
    match t with
    | TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p' _)) =>
        if param_eqb p p' then Some p else None
    | _ => None
    end.

(* A type argument of a supertype of `sub`: a type parameter of `sub`, or a type argument that
   doesn't mention any *)
Definition template_argument (sub: Class) (t: EType): bool :=
    match template_parameter t with
    | Some p => existsb (param_eqb p) (parameter_ids sub)
    | None => argument_in_fragment t && argument_concrete t
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
Hypothesis supertypes_are_templates: forall sub super,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length (supertype_arguments sub super) = length (parameter_ids super)
    /\ forall t, In t (supertype_arguments sub super) -> template_argument sub t = true.
Hypothesis supertypes_compose: forall a b c,
    a <> b -> b <> c -> a <> c -> a <> nothing -> b <> nothing ->
    base_type_is_subtype_of env a b = true -> base_type_is_subtype_of env b c = true ->
    supertype_arguments a c = map (instantiate env (bindings_of env b (supertype_arguments a b))) (supertype_arguments b c).

(* BoundTypeArgument.unify, once the ownerships are found to fit *)
Definition compare_variances (u: UnifyFn) (target_variance assignee_variance: Variance) (target assignee: EType) (s: VariableStates): option Unification :=
    match target_variance, assignee_variance with
    | invariant, invariant => match u target assignee (Ongoing s) with Some c => u assignee target c | None => None end
    | invariant, _ => Some Failed
    | output, output | output, invariant => u target assignee (Ongoing s)
    | output, input => Some Failed
    | input, input | input, invariant => u assignee target (Ongoing s)
    | input, output => Some Failed
    end.

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
    class_eqb c nothing = false /\ length arguments = length (parameter_ids c)
    /\ forall a, In a arguments -> argument_in_fragment a = true.
Proof.
    intros m c arguments H.
    change (negb (class_eqb c nothing) && Nat.eqb (length arguments) (length (type_parameters (declaration_of env c)))
        && forallb argument_in_fragment arguments = true) in H.
    apply andb_true_iff in H. destruct H as [H Ha]. apply andb_true_iff in H. destruct H as [Hc Hl].
    split; [|split].
    - destruct (class_eqb c nothing); [discriminate Hc|reflexivity].
    - unfold parameter_ids. rewrite length_map. apply Nat.eqb_eq, Hl.
    - apply forallb_forall, Ha.
Qed.

Lemma fragment_cases: forall t, in_fragment t = true ->
    (exists m c arguments, t = RootResolved m c arguments) \/
    (exists m c arguments, t = Nullable (RootResolved m c arguments) /\ in_fragment (RootResolved m c arguments) = true).
Proof.
    intros [m c arguments|[m c arguments| | | | | |]| | | | |] H; simpl in H; try discriminate H.
    - left. exists m, c, arguments. reflexivity.
    - right. exists m, c, arguments. split; [reflexivity|exact H].
Qed.

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

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating supertypes picks type arguments                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Definition is_type_argument (t: EType): bool :=
    match t with TypeArgument _ _ _ => true | _ => false end.

Lemma argument_in_fragment_is_type_argument: forall a, argument_in_fragment a = true -> is_type_argument a = true.
Proof. intros [| | | | | |] H; simpl in H; try discriminate H; reflexivity. Qed.

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
    \/ (template_parameter t = None /\ argument_in_fragment t = true /\ argument_concrete t = true).
Proof.
    intros sub t H. unfold template_argument in H. destruct (template_parameter t) as [p|] eqn:E.
    - left. destruct (template_parameter_some t p E) as [bp ->]. apply existsb_exists in H.
      destruct H as [q [Hq Hpq]]. apply param_eqb_eq in Hpq. subst q.
      apply In_nth_error in Hq. destruct Hq as [k Hk]. exists p, bp, k. auto.
    - right. apply andb_true_iff in H. tauto.
Qed.

Lemma template_is_type_argument: forall sub t, template_argument sub t = true -> is_type_argument t = true.
Proof.
    intros sub t H. destruct (template_kind sub t H) as [[p [bp [k [-> _]]]]|[_ [Hf _]]];
        [reflexivity|apply argument_in_fragment_is_type_argument, Hf].
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
    apply (lookup_in_bindings (parameter_ids sub) ys k); [apply parameter_ids_are_distinct|exact Hp|exact Hy].
Qed.

Lemma nth_error_same_length: forall {A B: Type} (l: list A) (l': list B) k a,
    length l = length l' -> nth_error l k = Some a -> exists b, nth_error l' k = Some b.
Proof.
    intros A B l l' k a Hl H. destruct (nth_error l' k) as [b|] eqn:E; [exists b; reflexivity|].
    apply nth_error_None in E. assert (k < length l) by (apply nth_error_Some; congruence). lia.
Qed.

Lemma map_identity: forall {A: Type} (f: A -> A) l, (forall a, In a l -> f a = a) -> map f l = l.
Proof. intros A f l H. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros a' Ha'. apply H. right. exact Ha'. Qed.

Lemma instantiate_class: forall b m c arguments,
    instantiate env b (RootResolved m c arguments) = RootResolved m c (map (instantiate env b) arguments).
Proof. reflexivity. Qed.

(* The fragment has no type parameters, so instantiating widens none of its type arguments *)
Lemma fragment_mentions_no_parameters: forall b k t,
    depth t <= k -> in_fragment t = true -> mentions_variantly_bound b t = false.
Proof.
    intros b k. induction k as [|k IH]; intros t Hd Ht.
    { exfalso. destruct (fragment_cases t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]]; simpl in Hd; lia. }
    destruct (fragment_cases t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
    - destruct (root_in_fragment m c arguments Ht) as [_ [_ Hargs]].
      apply not_true_iff_false. intros H. change (existsb (mentions_variantly_bound b) arguments = true) in H.
      apply existsb_exists in H. destruct H as [a [Ha Hm]].
      pose proof (argument_depth_below m c arguments a Ha) as Hda. specialize (Hargs a Ha).
      destruct a as [| | | |v o n| |]; simpl in Hargs; try discriminate Hargs.
      cbn [argument_depth] in Hda. simpl in Hm. rewrite (IH n) in Hm; [discriminate Hm|lia|exact Hargs].
    - rewrite depth_nullable in Hd. change (mentions_variantly_bound b (RootResolved m c arguments) = false).
      apply IH; [lia|exact Ht'].
Qed.

Lemma instantiate_argument_class: forall b v o m c arguments,
    in_fragment (RootResolved m c arguments) = true ->
    instantiate env b (TypeArgument v o (RootResolved m c arguments))
    = TypeArgument v (instantiate_ownership b o) (instantiate env b (RootResolved m c arguments)).
Proof.
    intros b v o m c arguments Ht.
    pose proof (fragment_mentions_no_parameters b _ _ (le_n _) Ht) as Hv.
    change (mentions_variantly_bound_in_arguments b (RootResolved m c arguments) = false) in Hv.
    change (instantiate env b (TypeArgument v o (RootResolved m c arguments)))
        with (if mentions_variantly_bound_in_arguments b (RootResolved m c arguments)
              then match v with
                   | input => TypeArgument output (instantiate_ownership b o) top_type
                   | _ => TypeArgument output (instantiate_ownership b o) (RootResolved m c (map (instantiate env b) arguments))
                   end
              else TypeArgument v (instantiate_ownership b o) (RootResolved m c (map (instantiate env b) arguments))).
    rewrite Hv. reflexivity.
Qed.

Lemma instantiate_argument_nullable: forall b v o m c arguments,
    in_fragment (RootResolved m c arguments) = true ->
    instantiate env b (TypeArgument v o (Nullable (RootResolved m c arguments)))
    = TypeArgument v (instantiate_ownership b o) (Nullable (instantiate env b (RootResolved m c arguments))).
Proof.
    intros b v o m c arguments Ht.
    pose proof (fragment_mentions_no_parameters b _ _ (le_n _) Ht) as Hv.
    change (mentions_variantly_bound_in_arguments b (Nullable (RootResolved m c arguments)) = false) in Hv.
    change (instantiate env b (TypeArgument v o (Nullable (RootResolved m c arguments))))
        with (if mentions_variantly_bound_in_arguments b (Nullable (RootResolved m c arguments))
              then match v with
                   | input => TypeArgument output (instantiate_ownership b o) top_type
                   | _ => TypeArgument output (instantiate_ownership b o) (Nullable (RootResolved m c (map (instantiate env b) arguments)))
                   end
              else TypeArgument v (instantiate_ownership b o) (Nullable (RootResolved m c (map (instantiate env b) arguments)))).
    rewrite Hv. reflexivity.
Qed.

Lemma root_concrete: forall m c arguments,
    concrete (RootResolved m c arguments) = true -> forall a, In a arguments -> argument_concrete a = true.
Proof. intros m c arguments H. change (forallb argument_concrete arguments = true) in H. apply forallb_forall, H. Qed.

(* What mentions no type parameters stays as it is *)
Lemma instantiate_concrete_with_arguments: forall k,
    (forall t b, in_fragment t = true -> concrete t = true -> depth t <= k -> instantiate env b t = t)
    /\ (forall a b, argument_in_fragment a = true -> argument_concrete a = true -> argument_depth a <= k ->
        instantiate env b a = a).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t b Ht _ Hd. exfalso.
        destruct (fragment_cases t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]]; simpl in Hd; lia.
      - intros [| | | |v o n| |] b Ha _ Hd; simpl in Ha, Hd; try discriminate Ha; lia. }
    assert (Hroot: forall m c arguments b, in_fragment (RootResolved m c arguments) = true ->
        concrete (RootResolved m c arguments) = true -> depth (RootResolved m c arguments) <= S k ->
        instantiate env b (RootResolved m c arguments) = RootResolved m c arguments).
    { intros m c arguments b Hf Hc Hd. rewrite instantiate_class. f_equal. apply map_identity. intros a Ha.
      destruct (root_in_fragment m c arguments Hf) as [_ [_ Hargs]].
      pose proof (argument_depth_below m c arguments a Ha).
      apply IHa; [apply Hargs, Ha|apply (root_concrete m c arguments Hc a Ha)|lia]. }
    split.
    - intros t b Ht Hc Hd.
      destruct (fragment_cases t Ht) as [[m [c [arguments ->]]]|[m [c [arguments [-> Ht']]]]].
      + exact (Hroot m c arguments b Ht Hc Hd).
      + change (rewrap_nullable (instantiate env b (RootResolved m c arguments)) = Nullable (RootResolved m c arguments)).
        rewrite depth_nullable in Hd. rewrite (Hroot m c arguments b Ht' Hc); [reflexivity|lia].
    - intros [| | | |v o n| |] b Ha Hc Hd; simpl in Ha, Hc, Hd; try discriminate Ha.
      apply andb_true_iff in Hc. destruct Hc as [Ho Hc].
      assert (Ho': instantiate_ownership b o = o) by (destruct o; try reflexivity; discriminate Ho).
      destruct (fragment_cases n Ha) as [[m [c [arguments ->]]]|[m [c [arguments [-> Hn']]]]].
      + rewrite (instantiate_argument_class b v o m c arguments Ha), Ho', (Hroot m c arguments b Ha Hc); [reflexivity|lia].
      + rewrite (instantiate_argument_nullable b v o m c arguments Hn'), Ho', (Hroot m c arguments b Hn' Hc); [reflexivity|].
        rewrite depth_nullable in Hd. lia.
Qed.

Lemma instantiate_concrete_argument: forall a b,
    argument_in_fragment a = true -> argument_concrete a = true -> instantiate env b a = a.
Proof. intros a b Ha Hc. exact (proj2 (instantiate_concrete_with_arguments (argument_depth a)) a b Ha Hc (le_n _)). Qed.

(* Instantiating a type argument of a supertype with the type arguments of a reference to the
   subclass: either one of those, or what it was *)
Lemma template_instance: forall sub xs t,
    length xs = length (parameter_ids sub) -> (forall x, In x xs -> is_type_argument x = true) ->
    template_argument sub t = true ->
    (exists k x, nth_error xs k = Some x /\ instantiate env (bindings_of env sub xs) t = x)
    \/ (argument_in_fragment t = true /\ forall b, instantiate env b t = t).
Proof.
    intros sub xs t Hl Hxs Ht. destruct (template_kind sub t Ht) as [[p [bp [k [-> Hk]]]]|[_ [Hf Hc]]].
    - left. destruct (nth_error_same_length (parameter_ids sub) xs k p (eq_sym Hl) Hk) as [x Hx].
      exists k, x. split; [exact Hx|]. apply (selects sub xs p bp k x Hk Hx), Hxs. eapply nth_error_In. exact Hx.
    - right. split; [exact Hf|]. intros b. apply instantiate_concrete_argument; assumption.
Qed.

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
    destruct (template_instance sub xs t Hl) as [[k [x [Hx ->]]]|[Hf ->]]; auto.
    - intros x Hx. apply argument_in_fragment_is_type_argument, Hxs, Hx.
    - apply Hxs. eapply nth_error_In. exact Hx.
Qed.

(* A supertype of a supertype, as one of the subclass directly *)
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
    apply map_ext_in. intros t Ht.
    assert (Hxs': forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply argument_in_fragment_is_type_argument, Hxs, Hx).
    destruct (template_kind b t (Htbc t Ht)) as [[p [bp [k [-> Hk]]]]|[_ [Hf Hc]]].
    - destruct (nth_error_same_length (parameter_ids b) (supertype_arguments a b) k p (eq_sym Hlab) Hk) as [u Hu].
      pose proof (Htab u (nth_error_In _ _ Hu)) as Htu.
      rewrite (selects b (supertype_arguments a b) p bp k u Hk Hu (template_is_type_argument a u Htu)).
      assert (Hu': nth_error (map (instantiate env (bindings_of env a xs)) (supertype_arguments a b)) k
          = Some (instantiate env (bindings_of env a xs) u)) by (rewrite nth_error_map, Hu; reflexivity).
      rewrite (selects b _ p bp k _ Hk Hu'); [reflexivity|].
      destruct (template_instance a xs u Hl Hxs' Htu) as [[j [x [Hx ->]]]|[Hfu ->]].
      + apply Hxs'. eapply nth_error_In. exact Hx.
      + apply argument_in_fragment_is_type_argument, Hfu.
    - rewrite (instantiate_concrete_argument t (bindings_of env b (supertype_arguments a b)) Hf Hc).
      rewrite !(instantiate_concrete_argument t _ Hf Hc). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify on the fragment, one step                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma unify_classes: forall n mt ct targs ma ca aargs s,
    class_eqb ca nothing = false ->
    unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) =
    if base_type_is_subtype_of env ca ct then
        if Model.is_subtype_of (mutability_of env (RootResolved ma ca aargs)) (mutability_of env (RootResolved mt ct targs))
        then unify_arguments (unify env n) targs
            (if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) s
        else Some Failed
    else Some Failed.
Proof.
    intros n mt ct targs ma ca aargs s Hca. rewrite unify_step_once. unfold unify_step, unify_root_resolved.
    destruct (base_type_is_subtype_of env ca ct); [|reflexivity]. cbn [negb].
    destruct (Model.is_subtype_of _ _); [|reflexivity]. cbn [negb]. rewrite Hca. reflexivity.
Qed.

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
      + destruct (root_in_fragment _ _ _ Ht) as [_ [_ Htargs]].
        destruct (root_in_fragment _ _ _ Ha) as [Hca [Hla Haargs]].
        rewrite unify_classes in H by exact Hca.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        * rewrite class_eqb_refl in H. apply (arguments_keep_states n targs aargs s u); [|exact H].
          intros t' a' s0 u0 Ht' Ha'. apply IHa; auto.
        * rewrite (class_eqb_false _ _ Hne) in H.
          destruct (supertype_arguments_in_fragment ca ct aargs Hne (class_eqb_false_neq _ _ Hca) Hb Hla Haargs)
              as [_ Hnorm].
          apply (arguments_keep_states n targs (parameterized_supertype_arguments env ca aargs ct) s u); [|exact H].
          intros t' a' s0 u0 Ht' Ha'. apply IHa; auto.
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_class in H. exact (IHt _ _ s u Ht' Ha H).
      + rewrite unify_nullable_nullable in H. exact (IHt _ _ s u Ht' Ha' H).
    - intros [| | | |vt ot nt| |] [| | | |va oa na| |] s u Ht Ha H; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha.
      rewrite unify_type_arguments in H. destruct (ownership_is_assignable_to oa ot); [|discriminate H].
      destruct vt, va; unfold compare_variances in H; try discriminate H;
          try exact (IHt _ _ s u Ht Ha H); try exact (IHt _ _ s u Ha Ht H).
      destruct (unify env n nt na (Ongoing s)) as [[w|]|] eqn:E; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
      pose proof (IHt _ _ s w Ht Ha E). subst w. exact (IHt _ _ s u Ha Ht H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Transitivity                                                                                     *)
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

(* Instantiating the type arguments of a supertype keeps a relation between the type arguments of
   two references to the subclass, where it holds of every type argument to itself *)
Lemma supertype_arguments_pairwise: forall (R: EType -> EType -> Prop) sub super xs ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids sub) -> length ys = length (parameter_ids sub) ->
    (forall x, In x xs -> is_type_argument x = true) -> (forall y, In y ys -> is_type_argument y = true) ->
    (forall t, R t t) ->
    Forall2 R xs ys ->
    Forall2 R (parameterized_supertype_arguments env sub xs super) (parameterized_supertype_arguments env sub ys super).
Proof.
    intros R sub super xs ys Hne Hn Hb Hlx Hly Hxs Hys Hrefl H.
    destruct (supertypes_are_templates sub super Hne Hn Hb) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq.
    induction (supertype_arguments sub super) as [|t ts IH]; simpl; constructor.
    - destruct (template_kind sub t (Ht t (or_introl eq_refl))) as [[p [bp [k [-> Hk]]]]|[_ [Hf Hc]]].
      + destruct (nth_error_same_length _ xs k p (eq_sym Hlx) Hk) as [x Hx].
        destruct (nth_error_same_length _ ys k p (eq_sym Hly) Hk) as [y Hy].
        rewrite (selects sub xs p bp k x Hk Hx), (selects sub ys p bp k y Hk Hy).
        * exact (Forall2_nth_error R xs ys k x y H Hx Hy).
        * apply Hys. eapply nth_error_In. exact Hy.
        * apply Hxs. eapply nth_error_In. exact Hx.
      + rewrite !instantiate_concrete_argument by assumption. apply Hrefl.
    - apply IH. intros t' Ht'. apply Ht. right. exact Ht'.
Qed.

Lemma compare_variances_transitive: forall (u1 u2 u3: UnifyFn) v1 v2 v3 x y z s,
    (forall t a, u1 t a Failed = Some Failed) -> (forall t a, u2 t a Failed = Some Failed) ->
    (forall w, u1 y x (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (forall w, u2 z y (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (u1 y x (Ongoing s) = Some (Ongoing s) -> u2 z y (Ongoing s) = Some (Ongoing s) -> u3 z x (Ongoing s) = Some (Ongoing s)) ->
    (u2 y z (Ongoing s) = Some (Ongoing s) -> u1 x y (Ongoing s) = Some (Ongoing s) -> u3 x z (Ongoing s) = Some (Ongoing s)) ->
    compare_variances u1 v2 v1 y x s = Some (Ongoing s) ->
    compare_variances u2 v3 v2 z y s = Some (Ongoing s) ->
    compare_variances u3 v3 v1 z x s = Some (Ongoing s).
Proof.
    intros u1 u2 u3 v1 v2 v3 x y z s Hf1 Hf2 Hk1 Hk2 Hforward Hbackward H1 H2.
    destruct v1, v2, v3; unfold compare_variances in *; try discriminate H1; try discriminate H2;
        repeat match goal with
        | H: match u1 _ _ (Ongoing s) with Some _ => _ | None => None end = Some (Ongoing s) |- _ =>
            apply both_ways in H; [destruct H|exact Hf1|exact Hk1]
        | H: match u2 _ _ (Ongoing s) with Some _ => _ | None => None end = Some (Ongoing s) |- _ =>
            apply both_ways in H; [destruct H|exact Hf2|exact Hk2]
        end;
        first [rewrite Hforward by assumption; apply Hbackward; assumption | apply Hforward; assumption | apply Hbackward; assumption].
Qed.

Definition nullable_bit (t: EType): nat := match t with Nullable _ => 1 | _ => 0 end.

(* By induction on the type in the middle: the assignee and the target may come from instantiated
   supertypes, which aren't part of the types compared *)
Lemma transitivity_with_arguments: forall k,
    (forall x y z n1 n2 s,
        in_fragment x = true -> in_fragment y = true -> in_fragment z = true ->
        2 * depth y + nullable_bit z <= k ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s))
    /\ (forall x y z n1 n2 s,
        argument_in_fragment x = true -> argument_in_fragment y = true -> argument_in_fragment z = true ->
        2 * argument_depth y <= k ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s)).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros x y z n1 n2 s _ Hy _ Hd. exfalso.
        destruct (fragment_cases y Hy) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]]; simpl in Hd; lia.
      - intros x [| | | |v o n| |] z n1 n2 s _ Hy _ Hd; simpl in Hy, Hd; try discriminate Hy; lia. }
    split.
    - intros x y z n1 n2 s Hx Hy Hz Hd H1 H2.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      change (S n1' + S n2') with (S (n1' + S n2')).
      destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
          destruct (fragment_cases y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> Hy']]]]];
          destruct (fragment_cases x Hx) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> Hx']]]]];
          rewrite ?depth_nullable in Hd; cbn [nullable_bit] in Hd;
          try (rewrite unify_class_nullable in H1; discriminate H1);
          try (rewrite unify_class_nullable in H2; discriminate H2).
      + (* three class types *)
        destruct (root_in_fragment _ _ _ Hx) as [Hcx [Hlx Hxargs]].
        destruct (root_in_fragment _ _ _ Hy) as [Hcy [Hly Hyargs]].
        destruct (root_in_fragment _ _ _ Hz) as [Hcz [Hlz Hzargs]].
        apply class_eqb_false_neq in Hcx, Hcy, Hcz.
        rewrite unify_classes in H1, H2 |- * by (apply class_eqb_false; assumption).
        destruct (base_type_is_subtype_of env cx cy) eqn:Hb1; [|discriminate H1].
        destruct (base_type_is_subtype_of env cy cz) eqn:Hb2; [|discriminate H2].
        rewrite (base_type_is_subtype_of_trans cx cy cz Hb1 Hb2).
        destruct (Model.is_subtype_of (mutability_of env (RootResolved mx cx xargs)) (mutability_of env (RootResolved my cy yargs))) eqn:Hm1;
            [|discriminate H1].
        destruct (Model.is_subtype_of (mutability_of env (RootResolved my cy yargs)) (mutability_of env (RootResolved mz cz zargs))) eqn:Hm2;
            [|discriminate H2].
        rewrite (mutability_trans _ _ _ Hm1 Hm2).
        (* x, as a reference to the class of y *)
        set (xs1 := if class_eqb cx cy then xargs else parameterized_supertype_arguments env cx xargs cy) in H1.
        assert (Hxs1: length xs1 = length (parameter_ids cy) /\ forall a, In a xs1 -> argument_in_fragment a = true).
        { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy]; [rewrite class_eqb_refl; auto|].
          rewrite (class_eqb_false _ _ Hxy). apply supertype_arguments_in_fragment; assumption. }
        destruct Hxs1 as [Hlxs1 Hfxs1].
        (* each of them takes the place of the corresponding type argument of y *)
        assert (Hpairs: Forall2 (fun x' y' => forall z', In z' zargs ->
                unify env n2' z' y' (Ongoing s) = Some (Ongoing s) -> unify env (n1' + S n2') z' x' (Ongoing s) = Some (Ongoing s))
            xs1 yargs).
        { apply (Forall2_impl_in (fun a t => unify env n1' t a (Ongoing s) = Some (Ongoing s))).
          - apply (pairwise_of_arguments n1' yargs xs1 s); [congruence| |exact H1].
            intros t a w Ht Ha. apply (proj2 (keeps_states_with_arguments n1')); auto.
          - intros x' y' Hx' Hy' E1 z' Hz' E2. apply (unify_fuel_monotone env (n1' + n2')); [lia|].
            pose proof (argument_depth_below my cy yargs y' Hy').
            apply (IHa x' y' z' n1' n2' s); auto; lia. }
        assert (Hk2: forall y' z' w, In y' yargs -> In z' zargs -> unify env n2' z' y' (Ongoing s) = Some (Ongoing w) -> w = s)
            by (intros y' z' w Hy' Hz'; apply (proj2 (keeps_states_with_arguments n2')); auto).
        destruct (Class_eq_dec cy cz) as [<-|Hyz].
        * (* y and z are of the same class: x takes the place of y as it is *)
          rewrite class_eqb_refl in H2.
          apply (arguments_forward n2' (n1' + S n2') zargs xs1 yargs s Hpairs zargs (incl_refl _) Hk2 H2).
        * (* y is of a subclass of z: x, as a reference to the class of y, takes its place in the supertype *)
          rewrite (class_eqb_false _ _ Hyz) in H2.
          destruct (Class_eq_dec cx cz) as [<-|Hxz].
          { exfalso. apply Hyz. apply acyclic; assumption. }
          rewrite (class_eqb_false _ _ Hxz).
          replace (parameterized_supertype_arguments env cx xargs cz) with (parameterized_supertype_arguments env cy xs1 cz).
          2: { unfold xs1. destruct (Class_eq_dec cx cy) as [<-|Hxy]; [rewrite class_eqb_refl; reflexivity|].
               rewrite (class_eqb_false _ _ Hxy). symmetry.
               apply parameterized_supertype_arguments_compose; assumption. }
          destruct (supertype_arguments_in_fragment cy cz yargs Hyz Hcy Hb2 Hly Hyargs) as [_ Hfys].
          apply (arguments_forward n2' (n1' + S n2') zargs _ (parameterized_supertype_arguments env cy yargs cz) s);
              [|apply incl_refl| |exact H2].
          -- apply supertype_arguments_pairwise; try assumption.
             ++ intros a Ha. apply argument_in_fragment_is_type_argument, Hfxs1, Ha.
             ++ intros a Ha. apply argument_in_fragment_is_type_argument, Hyargs, Ha.
             ++ intros t z' _ E. apply (unify_fuel_monotone env n2'); [lia|exact E].
          -- intros y' z' w Hy' Hz'. apply (proj2 (keeps_states_with_arguments n2')); auto.
      + (* two class types to a nullable type *)
        rewrite unify_nullable_class in H2 |- *.
        replace (n1' + S n2') with (S n1' + n2') by lia.
        apply (IHt _ _ _ (S n1') n2' s Hx Hy Hz'); [cbn [nullable_bit]; lia|exact H1|exact H2].
      + (* a class type to a nullable type to a nullable type *)
        rewrite unify_nullable_class in H1 |- *. rewrite unify_nullable_nullable in H2.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt _ _ _ n1' n2' s Hx Hy' Hz'); [cbn [nullable_bit]; lia|exact H1|exact H2].
      + (* three nullable types *)
        rewrite unify_nullable_nullable in H1, H2 |- *.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt _ _ _ n1' n2' s Hx' Hy' Hz'); [cbn [nullable_bit]; lia|exact H1|exact H2].
    - intros [| | | |v1 o1 x| |] [| | | |v2 o2 y| |] [| | | |v3 o3 z| |] n1 n2 s Hx Hy Hz Hd H1 H2;
          simpl in Hx, Hy, Hz, Hd; try discriminate Hx; try discriminate Hy; try discriminate Hz.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      change (S n1' + S n2') with (S (n1' + S n2')).
      rewrite unify_type_arguments in H1, H2 |- *.
      destruct (ownership_is_assignable_to o1 o2) eqn:Ho12; [|discriminate H1].
      destruct (ownership_is_assignable_to o2 o3) eqn:Ho23; [|discriminate H2].
      rewrite (ownership_trans o1 o2 o3 Ho12 Ho23).
      assert (Hbit: forall t, nullable_bit t <= 1) by (intros []; simpl; lia).
      apply (compare_variances_transitive (unify env n1') (unify env n2') (unify env (n1' + S n2')) v1 v2 v3 x y z s);
          try assumption.
      + apply unify_keeps_failure.
      + apply unify_keeps_failure.
      + intros w. apply (proj1 (keeps_states_with_arguments n1')); assumption.
      + intros w. apply (proj1 (keeps_states_with_arguments n2')); assumption.
      + intros E1 E2. apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        pose proof (Hbit z). apply (IHt x y z n1' n2' s); auto; lia.
      + intros E2 E1. apply (unify_fuel_monotone env (n2' + n1')); [lia|].
        pose proof (Hbit x). apply (IHt z y x n2' n1' s); auto; lia.
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
    rewrite (proj1 (transitivity_with_arguments (2 * depth y + nullable_bit z)) x y z n1 n2 [] Hx Hy Hz (le_n _) E1 E2).
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
    - destruct (template_kind sub t (Ht t (or_introl eq_refl))) as [[p [bp [k [-> Hk]]]]|[Hnone [Hf Hc]]].
      + destruct (nth_error_same_length _ xs k p (eq_sym Hl) Hk) as [x Hx].
        rewrite (selects sub xs p bp k x Hk Hx) by (apply argument_in_fragment_is_type_argument, Hxs; eapply nth_error_In; exact Hx).
        assert (Htp: template_parameter (TypeArgument Model.invariant (parameter_ownership p) (Generic (mkGenericRef None p bp))) = Some p)
            by (simpl; unfold param_eqb; rewrite Nat.eqb_refl; reflexivity).
        unfold template_meets in Hpt. rewrite Htp in Hpt.
        intros o Ho. specialize (Hpt o Ho).
        pose proof (prescription_of_nth (type_parameters (declaration_of env sub)) k p (parameter_ids_are_distinct sub) Hk) as Hpk.
        rewrite Hpt in Hpk.
        exact (Forall2_nth_error meets (prescriptions sub) xs k (Some o) x Hm Hpk Hx o eq_refl).
      + rewrite instantiate_concrete_argument by assumption. unfold template_meets in Hpt. rewrite Hnone in Hpt. exact Hpt.
    - apply IH. intros t' Ht'. apply Ht. right. exact Ht'.
Qed.

End Transitivity.

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
(* - the supertypes are transitive, and Any has none;                                              *)
(* - only classes without type parameters are supertypes of other classes.                        *)
(* The last one is a restriction: comparing a class type to a type of a proper supertype goes     *)
(* through the type arguments of the supertype, as instantiated with those of the subtype. Beyond  *)
(* it, transitivity needs that finding a supertype of a supertype agrees with finding it directly, *)
(* and that instantiating with assignable type arguments gives assignable types.                   *)
(* ---------------------------------------------------------------------------------------------- *)

Section Transitivity.

Variable env: Environment.

Hypothesis supertypes_are_transitive: forall a b c,
    In b (supertypes_of env a) -> In c (supertypes_of env b) -> In c (supertypes_of env a).
Hypothesis any_has_no_supertypes: supertypes_of env any = [].
Hypothesis no_generic_supertypes: forall c c',
    c <> c' -> c <> nothing -> base_type_is_subtype_of env c c' = true -> type_parameters (declaration_of env c') = [].

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

Lemma no_arguments_across_classes: forall c c' (arguments: list EType),
    c <> c' -> c <> nothing -> base_type_is_subtype_of env c c' = true ->
    length arguments = length (type_parameters (declaration_of env c')) -> arguments = [].
Proof.
    intros c c' arguments Hne Hn Hb Hl. rewrite (no_generic_supertypes c c' Hne Hn Hb) in Hl.
    destruct arguments; [reflexivity|discriminate Hl].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts about the fragment                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma root_in_fragment: forall m c arguments,
    in_fragment (RootResolved m c arguments) = true ->
    class_eqb c nothing = false /\ length arguments = length (type_parameters (declaration_of env c))
    /\ forall a, In a arguments -> argument_in_fragment a = true.
Proof.
    intros m c arguments H.
    change (negb (class_eqb c nothing) && Nat.eqb (length arguments) (length (type_parameters (declaration_of env c)))
        && forallb argument_in_fragment arguments = true) in H.
    apply andb_true_iff in H. destruct H as [H Ha]. apply andb_true_iff in H. destruct H as [Hc Hl].
    split; [|split].
    - destruct (class_eqb c nothing); [discriminate Hc|reflexivity].
    - apply Nat.eqb_eq, Hl.
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
      + destruct (root_in_fragment _ _ _ Ht) as [_ [Hlt Htargs]].
        destruct (root_in_fragment _ _ _ Ha) as [Hca [_ Haargs]].
        rewrite unify_classes in H by exact Hca.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hb; [|discriminate H].
        destruct (Model.is_subtype_of _ _); [|discriminate H].
        destruct (Class_eq_dec ca ct) as [<-|Hne].
        * rewrite class_eqb_refl in H. apply (arguments_keep_states n targs aargs s u); [|exact H].
          intros t' a' s0 u0 Ht' Ha'. apply IHa; auto.
        * rewrite (no_arguments_across_classes ca ct targs Hne (class_eqb_false_neq _ _ Hca) Hb Hlt) in H.
          injection H as ->. reflexivity.
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

Lemma arguments_transitive: forall n1 n2 n3 xs ys zs s,
    length ys = length xs -> length zs = length ys ->
    (forall x y z, In x xs -> In y ys -> In z zs ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) -> unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env n3 z x (Ongoing s) = Some (Ongoing s)) ->
    (forall x y w, In x xs -> In y ys -> unify env n1 y x (Ongoing s) = Some (Ongoing w) -> w = s) ->
    (forall y z w, In y ys -> In z zs -> unify env n2 z y (Ongoing s) = Some (Ongoing w) -> w = s) ->
    unify_arguments (unify env n1) ys xs s = Some (Ongoing s) ->
    unify_arguments (unify env n2) zs ys s = Some (Ongoing s) ->
    unify_arguments (unify env n3) zs xs s = Some (Ongoing s).
Proof.
    intros n1 n2 n3 xs. induction xs as [|x xs IH]; intros [|y ys] [|z zs] s Hl1 Hl2 Htrans Hk1 Hk2 H1 H2;
        simpl in Hl1, Hl2; try discriminate; [reflexivity|].
    unfold unify_arguments in *. simpl in H1, H2 |- *.
    destruct (unify env n1 y x (Ongoing s)) as [[w|]|] eqn:E1; [|rewrite fold_stays_failed in H1; discriminate H1|discriminate H1].
    pose proof (Hk1 x y w (or_introl eq_refl) (or_introl eq_refl) E1). subst w.
    destruct (unify env n2 z y (Ongoing s)) as [[w|]|] eqn:E2; [|rewrite fold_stays_failed in H2; discriminate H2|discriminate H2].
    pose proof (Hk2 y z w (or_introl eq_refl) (or_introl eq_refl) E2). subst w.
    rewrite (Htrans x y z (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) E1 E2).
    apply (IH ys zs s); try lia; try assumption.
    - intros x' y' z' Hx Hy Hz. apply Htrans; right; assumption.
    - intros x' y' w Hx Hy. apply Hk1; right; assumption.
    - intros y' z' w Hy Hz. apply Hk2; right; assumption.
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

Lemma transitivity_with_arguments: forall k,
    (forall x y z n1 n2 s,
        in_fragment x = true -> in_fragment y = true -> in_fragment z = true ->
        depth x + depth y + depth z <= k ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s))
    /\ (forall x y z n1 n2 s,
        argument_in_fragment x = true -> argument_in_fragment y = true -> argument_in_fragment z = true ->
        argument_depth x + argument_depth y + argument_depth z <= k ->
        unify env n1 y x (Ongoing s) = Some (Ongoing s) ->
        unify env n2 z y (Ongoing s) = Some (Ongoing s) ->
        unify env (n1 + n2) z x (Ongoing s) = Some (Ongoing s)).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros x y z n1 n2 s Hx _ _ Hd. exfalso.
        destruct (fragment_cases x Hx) as [[m [c [arguments ->]]]|[m [c [arguments [-> _]]]]]; simpl in Hd; lia.
      - intros [| | | |v o n| |] y z n1 n2 s Hx _ _ Hd; simpl in Hx, Hd; try discriminate Hx; lia. }
    split.
    - intros x y z n1 n2 s Hx Hy Hz Hd H1 H2.
      destruct n1 as [|n1']; [discriminate H1|]. destruct n2 as [|n2']; [discriminate H2|].
      change (S n1' + S n2') with (S (n1' + S n2')).
      destruct (fragment_cases z Hz) as [[mz [cz [zargs ->]]]|[mz [cz [zargs [-> Hz']]]]];
          destruct (fragment_cases y Hy) as [[my [cy [yargs ->]]]|[my [cy [yargs [-> Hy']]]]];
          destruct (fragment_cases x Hx) as [[mx [cx [xargs ->]]]|[mx [cx [xargs [-> Hx']]]]];
          rewrite ?depth_nullable in Hd;
          try (rewrite unify_class_nullable in H1; discriminate H1);
          try (rewrite unify_class_nullable in H2; discriminate H2).
      + (* three class types *)
        destruct (root_in_fragment _ _ _ Hx) as [Hcx [Hlx Hxargs]].
        destruct (root_in_fragment _ _ _ Hy) as [Hcy [Hly Hyargs]].
        destruct (root_in_fragment _ _ _ Hz) as [Hcz [Hlz Hzargs]].
        rewrite unify_classes in H1, H2 |- * by assumption.
        destruct (base_type_is_subtype_of env cx cy) eqn:Hb1; [|discriminate H1].
        destruct (base_type_is_subtype_of env cy cz) eqn:Hb2; [|discriminate H2].
        rewrite (base_type_is_subtype_of_trans cx cy cz Hb1 Hb2).
        destruct (Model.is_subtype_of (mutability_of env (RootResolved mx cx xargs)) (mutability_of env (RootResolved my cy yargs))) eqn:Hm1;
            [|discriminate H1].
        destruct (Model.is_subtype_of (mutability_of env (RootResolved my cy yargs)) (mutability_of env (RootResolved mz cz zargs))) eqn:Hm2;
            [|discriminate H2].
        rewrite (mutability_trans _ _ _ Hm1 Hm2).
        destruct (Class_eq_dec cy cz) as [<-|Hyz];
            [destruct (Class_eq_dec cx cy) as [<-|Hxy]|].
        * (* the same class: the type arguments are compared *)
          rewrite class_eqb_refl in H1, H2 |- *.
          apply (arguments_transitive n1' n2' (n1' + S n2') xargs yargs zargs s); try congruence; try assumption.
          -- intros x y z Hx' Hy' Hz' E1 E2. apply (unify_fuel_monotone env (n1' + n2')); [lia|].
             pose proof (argument_depth_below mx cx xargs x Hx').
             pose proof (argument_depth_below my cx yargs y Hy').
             pose proof (argument_depth_below mz cx zargs z Hz').
             apply (IHa x y z n1' n2' s); auto; lia.
          -- intros x y w Hx' Hy'. apply (proj2 (keeps_states_with_arguments n1')); auto.
          -- intros y z w Hy' Hz'. apply (proj2 (keeps_states_with_arguments n2')); auto.
        * (* a proper supertype has no type parameters *)
          rewrite (no_arguments_across_classes cx cy zargs Hxy (class_eqb_false_neq _ _ Hcx) Hb1 Hlz). reflexivity.
        * rewrite (no_arguments_across_classes cy cz zargs Hyz (class_eqb_false_neq _ _ Hcy) Hb2 Hlz). reflexivity.
      + (* two class types to a nullable type *)
        rewrite unify_nullable_class in H2 |- *.
        replace (n1' + S n2') with (S n1' + n2') by lia.
        apply (IHt _ _ _ (S n1') n2' s Hx Hy Hz'); [lia|exact H1|exact H2].
      + (* a class type to a nullable type to a nullable type *)
        rewrite unify_nullable_class in H1 |- *. rewrite unify_nullable_nullable in H2.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt _ _ _ n1' n2' s Hx Hy' Hz'); [lia|exact H1|exact H2].
      + (* three nullable types *)
        rewrite unify_nullable_nullable in H1, H2 |- *.
        apply (unify_fuel_monotone env (n1' + n2')); [lia|].
        apply (IHt _ _ _ n1' n2' s Hx' Hy' Hz'); [lia|exact H1|exact H2].
    - intros [| | | |v1 o1 x| |] [| | | |v2 o2 y| |] [| | | |v3 o3 z| |] n1 n2 s Hx Hy Hz Hd H1 H2;
          simpl in Hx, Hy, Hz, Hd; try discriminate Hx; try discriminate Hy; try discriminate Hz.
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
    rewrite (proj1 (transitivity_with_arguments (depth x + depth y + depth z)) x y z n1 n2 [] Hx Hy Hz (le_n _) E1 E2).
    reflexivity.
Qed.

End Transitivity.

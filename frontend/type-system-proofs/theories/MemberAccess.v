From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Member access                                                                                    *)
(*                                                                                                *)
(* An object is of a class C with exact type arguments xs (invariant, owned or ref), and its member *)
(* variables have the declared types instantiated with those. A reference to it may be of type     *)
(* C<ys>, with ys of any variance, as long as C<xs> is assignable to C<ys>. Through that reference, *)
(* BoundMemberVariableReadExpression and BoundObjectMemberAssignmentStatement instantiate the      *)
(* declared type of a member with ys instead. This shows that doing so is sound:                  *)
(* - what is read is no more than what the reference says (member_read_sound): an in-variant type *)
(*   argument reads as `read Any?` (Subtyping.read_type);                                          *)
(* - what is written fits the member of the actual object (member_write_sound): a type parameter  *)
(*   bound to a variant type argument inside the type arguments of the member makes it take       *)
(*   nothing but Nothing (BoundTypeArgument.instantiateAllParametersForWriting); one as the type    *)
(*   of the member takes values for an in-variant type argument, but not for an out-variant one.   *)
(* For members whose declared type is a type parameter of C, or a class type of type parameters of *)
(* C as Transitivity.template_type has them (`Box<T>`, `Map<K, Box<V>>?`), with types of the       *)
(* fragment of Transitivity.v; not for `T?` or variant type arguments in the declared type          *)
(* (`Box<out T>`). The mutability of what is read, and the ownership of the members, is up to       *)
(* Ownership.v. A value written isn't of a non-nullable Nothing, as there are no such values (the   *)
(* axiom that panic never returns): an out-variant type argument takes them, whatever their         *)
(* mutability.                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Section MemberAccess.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* A type argument of an object: invariant, owned or ref, of a type of the fragment *)
Definition is_exact_argument (x: EType): bool :=
    match x with
    | TypeArgument Model.invariant o n =>
        match o with owned | ref => in_fragment env n | _ => false end
    | _ => false
    end.

(* The declared type of a member of class c *)
Definition member_type (c: Class) (f: EType): bool :=
    match f with
    | Generic (mkGenericRef None p _) => existsb (param_eqb p) (parameter_ids env c)
    | _ => template_type env c f
    end.

(* The type read from a member, through a reference whose type arguments are the bindings *)
Definition read_member (b: Bindings) (f: EType): EType :=
    match instantiate env b f with
    | TypeArgument v _ x => read_type v x
    | t => t
    end.

(* The type written to a member, through a reference whose type arguments are the bindings
   (BoundTypeArgument.instantiateAllParametersForWriting) *)
Definition write_member (b: Bindings) (f: EType): EType :=
    if mentions_loosely_bound_in_arguments b f then
        match f with Nullable _ => Nullable bottom_type | _ => bottom_type end
    else instantiate env b f.

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

Lemma pairs_monotone: forall n n' s xs ys, n <= n' ->
    Forall2 (fun x y => unify env n y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys.
Proof.
    intros n n' s xs ys Hn H. eapply Forall2_impl; [|exact H]. intros x y E. exact (unify_fuel_monotone env n n' y x _ _ Hn E).
Qed.

(* Where the type arguments of the object are assignable to those of the reference, they can stand
   in for them (Transitivity.lifting) *)
Lemma receiver_leaves_lift: forall n1 s xs ys m,
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n1 y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    leaves_lift env m n1 s xs ys.
Proof.
    intros n1 s xs ys m Hxs Hys H. unfold leaves_lift.
    apply (Forall2_impl_in _ _ _ _ H). intros x y Hx Hy E.
    destruct (exact_argument_facts x (Hxs x Hx)) as [o [n [_ [_ [Hfx Hlx]]]]]. split.
    - intros z m' Hm' Hz E2. replace (m' + n1) with (n1 + m') by lia.
      apply (proj2 (transitivity_with_arguments env wf (n1 + m')) x y z n1 m' s); auto.
    - intros Hl. split; [exact Hlx|].
      intros z m' Hm' Hz E2. apply (proj2 (transitivity_with_arguments env wf (m' + n1)) z y x m' n1 s); auto.
      apply (exact_symmetric env wf); auto.
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

Lemma instantiate_parameter: forall b p bp a,
    lookup_binding b p = Some a -> instantiate env b (Generic (mkGenericRef None p bp)) = a.
Proof. intros b p bp a H. simpl. rewrite H. reflexivity. Qed.

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
Lemma parameter_member: forall n' s c xs ys p bp,
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    Forall2 (fun x y => unify env n' y x (Ongoing s) = Some (Ongoing s)) xs ys ->
    existsb (param_eqb p) (parameter_ids env c) = true ->
    exists o X v oy Y n'',
        instantiate env (bindings_of env c xs) (Generic (mkGenericRef None p bp)) = TypeArgument Model.invariant o X
        /\ instantiate env (bindings_of env c ys) (Generic (mkGenericRef None p bp)) = TypeArgument v oy Y
        /\ in_fragment env X = true /\ in_fragment env Y = true /\ n' = S n''
        /\ compare_variances (unify env n'') v Model.invariant Y X s = Some (Ongoing s).
Proof.
    intros n' s c xs ys p bp Hlx Hly Hxs Hys H Hp. destruct (member_parameter c p Hp) as [i Hi].
    destruct (nth_error_same_length _ xs i p (eq_sym Hlx) Hi) as [x Ex].
    destruct (nth_error_same_length _ ys i p (eq_sym Hly) Hi) as [y Ey].
    destruct (exact_argument_facts x (Hxs x (nth_error_In _ _ Ex))) as [o [X [-> [HX _]]]].
    pose proof (Hys y (nth_error_In _ _ Ey)) as Hy.
    destruct y as [| | | |v oy Y| |]; simpl in Hy; try discriminate Hy.
    pose proof (Forall2_nth_error _ xs ys i _ _ H Ex Ey) as E.
    destruct n' as [|n'']; [discriminate E|].
    rewrite unify_type_arguments in E. destruct (ownership_is_assignable_to o oy); [|discriminate E].
    exists o, X, v, oy, Y, n''. repeat split; auto.
    - apply instantiate_parameter. exact (lookup_parameter env wf c xs i p _ Hi Ex).
    - apply instantiate_parameter. exact (lookup_parameter env wf c ys i p _ Hi Ey).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Members typed as a class type                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma read_class_shaped: forall b t, class_shaped (instantiate env b t) -> read_member b t = instantiate env b t.
Proof.
    intros b t Hs. unfold read_member. destruct Hs as [[m [c [args E]]]|[m [c [args E]]]]; rewrite E; reflexivity.
Qed.

Lemma mentions_template: forall c b f, template_type env c f = true ->
    mentions_loosely_bound_in_arguments b f = mentions_loosely_bound b f.
Proof.
    intros c b f Ht. destruct (template_type_cases env c f Ht) as [[m [c' [args ->]]]|[m [c' [args [-> _]]]]]; reflexivity.
Qed.

(* `exclusive Nothing` is assignable to every type of the fragment *)
Lemma bottom_below: forall t f s, in_fragment env t = true -> 2 <= f -> unify env f t bottom_type (Ongoing s) = Some (Ongoing s).
Proof.
    intros t f s Ht Hf. apply (below_bottom env wf 1 bottom_type s (bottom_in_fragment env wf)); [|exact Ht|exact Hf].
    apply (proj1 (reflexivity_with_arguments env 1)); [exact (bottom_in_fragment env wf)|simpl; lia].
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
    destruct f as [| |[[gm|] p bp]| | | |]; cbn [member_type] in Hf; try (simpl in Hf; discriminate Hf).
    3: { (* a type parameter *)
        destruct (parameter_member n' s c xs ys p bp Hlx Hly Hxs Hys Hpairs Hf)
            as [o [X [v [oy [Y [n'' [Ex [Ey [HX [HY [-> Hcmp]]]]]]]]]]].
        unfold read_member. rewrite Ex, Ey. cbn [read_type].
        destruct v; unfold compare_variances in Hcmp; cbn [read_type].
        - split; [exact HX|]. split; [exact HY|]. exists n''.
          apply (both_ways (unify env n'') Y X s) in Hcmp; [apply Hcmp|apply unify_keeps_failure|].
          intros w. apply (proj1 (keeps_states_with_arguments env wf n'')); assumption.
        - split; [exact HX|]. split; [exact (top_in_fragment env wf)|]. exists 2.
          apply (above_top env wf 2 top_type s (top_in_fragment env wf)); [|exact HX|lia].
          apply (proj1 (reflexivity_with_arguments env 2)); [exact (top_in_fragment env wf)|simpl; lia].
        - split; [exact HX|]. split; [exact HY|]. exists n''. exact Hcmp. }
    all: rewrite !read_class_shaped by (apply (template_instance_shape env c); exact Hf).
    all: pose proof (template_type_instance_in_fragment env wf c xs _ Hlx Hfxs Hf) as Hfx;
         pose proof (template_type_instance_in_fragment env wf c ys _ Hly Hys Hf) as Hfy;
         split; [exact Hfx|]; split; [exact Hfy|].
    all: match goal with |- exists fuel, unify env fuel (instantiate env _ ?t) _ _ = _ =>
        set (k := depth (instantiate env (bindings_of env c ys) t));
        destruct (lifting env wf (S n') s ltac:(lia) k c xs ys Hlx Hly Hfxs Hys
            (receiver_leaves_lift (S n') s xs ys k Hxs Hys
                (pairs_monotone n' (S n') s xs ys ltac:(lia) Hpairs)))
            as [Hlift _];
        exists (k + S n'); apply (proj1 (Hlift t Hf) (instantiate env (bindings_of env c ys) t) k (le_n _) Hfy);
        apply (proj1 (reflexivity_with_arguments env k)); [exact Hfy|apply le_n] end.
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
 * reference is assignable to the member of the object.
 *)
Theorem member_write_sound: forall n s m c xs m' ys f V fuel,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing s) = Some (Ongoing s) ->
    member_type c f = true ->
    in_fragment env V = true -> is_non_nullable_nothing env V = false ->
    unify env fuel (write_member (bindings_of env c ys) f) V (Ongoing s) = Some (Ongoing s) ->
    exists fuel', unify env fuel' (read_member (bindings_of env c xs) f) V (Ongoing s) = Some (Ongoing s).
Proof.
    intros n s m c xs m' ys f V fuel Hc Hlx Hly Hxs Hys H Hf HV HVn HW.
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true)
        by (intros x Hx; destruct (exact_argument_facts x (Hxs x Hx)) as [? [? [_ [_ [? _]]]]]; assumption).
    destruct (receiver_arguments n s m c xs m' ys Hc ltac:(lia) Hfxs Hys H) as [n' [-> Hpairs]].
    destruct f as [| |[[gm|] p bp]| | | |]; cbn [member_type] in Hf; try (simpl in Hf; discriminate Hf).
    3: { (* a type parameter: an out-variant type argument takes nothing but Nothing *)
        destruct (parameter_member n' s c xs ys p bp Hlx Hly Hxs Hys Hpairs Hf)
            as [o [X [v [oy [Y [n'' [Ex [Ey [HX [HY [-> Hcmp]]]]]]]]]]].
        unfold write_member, read_member in *. cbn [mentions_loosely_bound_in_arguments] in HW.
        rewrite Ey in HW. rewrite Ex. cbn [read_type].
        destruct fuel as [|fuel]; [discriminate HW|]. rewrite (unify_argument_value fuel v oy Y V s HV) in HW.
        assert (HXY: unify env n'' X Y (Ongoing s) = Some (Ongoing s)).
        { destruct v; unfold compare_variances in Hcmp; simpl in HW.
          - apply (both_ways (unify env n'') Y X s) in Hcmp; [apply Hcmp|apply unify_keeps_failure|].
            intros w. apply (proj1 (keeps_states_with_arguments env wf n'')); assumption.
          - exact Hcmp.
          - rewrite HVn in HW. discriminate HW. }
        assert (HVY: unify env fuel Y V (Ongoing s) = Some (Ongoing s)) by (destruct v; simpl in HW; first [exact HW|rewrite HVn in HW; discriminate HW]).
        exists (fuel + n''). apply (proj1 (transitivity_with_arguments env wf (fuel + n'')) V Y X fuel n'' s); auto. }
    all: rewrite read_class_shaped by (apply (template_instance_shape env c); exact Hf).
    all: pose proof (template_type_instance_in_fragment env wf c xs _ Hlx Hfxs Hf) as Hfx.
    all: unfold write_member in HW; rewrite (mentions_template c _ _ Hf) in HW.
    all: pose proof (lifting env wf (S n') s ltac:(lia) fuel c xs ys Hlx Hly Hfxs Hys
             (receiver_leaves_lift (S n') s xs ys fuel Hxs Hys (pairs_monotone n' (S n') s xs ys ltac:(lia) Hpairs)))
             as [Hlift _].
    all: match goal with |- exists fuel', unify env fuel' (instantiate env _ ?t) _ _ = _ =>
        destruct (mentions_loosely_bound (bindings_of env c ys) t) eqn:Em;
        [try rewrite Em in HW; cbn beta iota in HW
        |exists (fuel + S n'); exact (proj2 (Hlift t Hf) Em V fuel (le_n _) HV HW)] end.
    - (* a class type: takes nothing but Nothing, which is assignable to the member of the object *)
      exists (fuel + 2).
      exact (proj1 (transitivity_with_arguments env wf (fuel + 2)) V bottom_type _ fuel 2 s (le_n _)
          HV (bottom_in_fragment env wf) Hfx HW (bottom_below _ 2 s Hfx (le_n _))).
    - (* a nullable class type: takes nothing but null and Nothing *)
      destruct (template_type_cases env c _ Hf) as [[m0 [c0 [a0 E]]]|[m0 [c0 [a0 [E _]]]]]; [discriminate E|].
      injection E as ->.
      match goal with |- exists _, unify env _ (instantiate env _ (Nullable (RootResolved ?m0 ?c0 ?a0))) _ _ = _ =>
          rewrite (instantiate_nullable_class env _ m0 c0 a0) in Hfx |- *;
          assert (Hfx': in_fragment env (RootResolved m0 c0 (map (instantiate env (bindings_of env c xs)) a0)) = true)
              by (change (is_class (RootResolved m0 c0 (map (instantiate env (bindings_of env c xs)) a0))
                      && in_fragment env (RootResolved m0 c0 (map (instantiate env (bindings_of env c xs)) a0)) = true) in Hfx;
                  apply andb_true_iff in Hfx; apply Hfx);
          assert (HN: in_fragment env (Nullable bottom_type) = true)
              by (change (is_class bottom_type && in_fragment env bottom_type = true); rewrite (bottom_in_fragment env wf); reflexivity);
          exists (fuel + 3);
          apply (proj1 (transitivity_with_arguments env wf (fuel + 3)) V (Nullable bottom_type) _ fuel 3 s (le_n _) HV HN Hfx HW);
          rewrite unify_nullable_nullable; apply bottom_below; [exact Hfx'|lia]
      end.
Qed.

End MemberAccess.

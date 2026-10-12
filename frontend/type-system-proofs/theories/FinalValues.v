From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Final values of inference, of type parameters and intersections                                  *)
(*                                                                                                *)
(* The final value of a type variable is its lower bound, or its upper one: closest common         *)
(* supertypes and intersections of the types of the arguments and of the declared bound. Those are *)
(* no class types of Transitivity.v in general, but type parameters and intersections, of the      *)
(* fragment of Fragment.v. Constraints.v takes the types variables are replaced with, and the      *)
(* bounds, as given; here they are those of Fragment.v, with the references to type parameters     *)
(* well-formed (Generics.v), and calling a member function with type parameters of its own is      *)
(* sound whatever its final values are (member_call_with_any_final_values_sound).                  *)
(*                                                                                                *)
(* That takes the bounds being the bounds they are meant to be in the success form of unify, not   *)
(* only in the form of never rejecting (transitivity_never_fails): a type below a lower bound is    *)
(* below the next one, and so on, which never rejecting doesn't chain over. So this rests on the   *)
(* conjectures of Conjectures.v: intersect and closestCommonSupertypeWith build types of the       *)
(* fragment, below and above the types they are made of, and unify terminates where inheritance    *)
(* isn't expansive. With them, unify is transitive and reflexive as usual on the fragment.         *)
(* ---------------------------------------------------------------------------------------------- *)

Section Reflexivity.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Lemma forall2_refl: forall {A: Type} (R: A -> A -> Prop) l, (forall a, In a l -> R a a) -> Forall2 R l l.
Proof.
    intros A R l H. induction l as [|a l IH]; constructor; [apply H; left; reflexivity|].
    apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

(* unify never rejects a type of the fragment of Fragment.v for itself *)
Lemma reflexive_never_fails: forall t, gfrag env t = true -> never_fails env t t.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm p bound]|me msg|v o n|g|cs]; simpl in H; try discriminate H.
    - (* a class type: its type arguments, each for itself *)
      destruct (root_gfrag env m c args H) as [Hl Hargs].
      assert (Hall: forall a, In a args -> never_fails env a a).
      { intros a Hin. pose proof (Hargs a Hin) as Ha. pose proof (esize_in args a Hin) as Hs.
        destruct a as [| | | |va oa na| |]; simpl in Ha; try discriminate Ha.
        assert (Hn: never_fails env na na) by (apply (IH (esize na)); [simpl in Hs |- *; lia|reflexivity|exact Ha]).
        apply never_fails_step. intros f s. rewrite gunify_type_arguments by exact Ha.
        rewrite ownership_is_assignable_to_itself.
        apply (compare_variances_never_fails env wf); [exact (gfrag_no_vars env _ Ha)|exact (gfrag_no_vars env _ Ha)|].
        destruct va; [split|..]; exact Hn. }
      apply never_fails_step. intros f s. rewrite unify_classes.
      replace (base_type_is_subtype_of env c c) with true by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
      rewrite mutability_is_subtype_of_refl. destruct (class_eqb c nothing); [discriminate|]. rewrite class_eqb_refl.
      apply (arguments_never_fail env wf); [reflexivity|exact (arguments_gfrag_no_vars env _ Hargs)|exact (arguments_gfrag_no_vars env _ Hargs)|].
      exact (forall2_refl _ args Hall).
    - (* a nullable type: the type it wraps *)
      apply andb_true_iff in H. destruct H as [_ Hn].
      apply never_fails_step. intros f s. rewrite unify_nullable_nullable.
      apply (IH (esize n)); [simpl; lia|reflexivity|exact Hn].
    - (* a reference to a type parameter: the same one, of the same mutability and nullability *)
      apply never_fails_step. intros f s. rewrite step_generic_generic, param_eqb_refl, mutability_is_subtype_of_refl.
      destruct (is_nullable bound); discriminate.
    - (* an intersection: each component takes it through itself *)
      apply (inter_target_never_fails env wf); [exact (gfrag_components_no_vars env _ H)|simpl; exact (gfrag_components_no_vars env _ H)|exact I|].
      intros c Hc. destruct (intersection_gfrag env cs H) as [_ Hcs]. destruct (Hcs c Hc) as [Hcomp Hgc].
      pose proof (esize_in cs c Hc) as Hs.
      assert (Hcc: never_fails env c c) by (apply (IH (esize c)); [simpl; lia|reflexivity|exact Hgc]).
      apply never_fails_step. intros f s.
      destruct (component_cases env c Hcomp Hgc) as [[mc [dc [cargs ->]]]|[gm [p [bound [-> _]]]]].
      + rewrite step_root_inter. apply (flipped_never_fails env f _ cs s _ Hc). apply Hcc.
      + rewrite step_generic_inter. apply (flipped_never_fails env f _ cs s _ Hc). apply Hcc.
Qed.

End Reflexivity.

Section FinalValues.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Let declared_gfrag := bw_gfrag env declared declared_wf.
Let declared_mutability := bw_mutability env declared declared_wf.

(* The conjectures of Conjectures.v *)
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.
Hypothesis intersect_in_fragment: intersect_stays_in_fragment env declared.
Hypothesis supertype_in_fragment: closest_common_supertype_stays_in_fragment env declared.
Hypothesis intersect_below: intersect_is_below_both env declared.
Hypothesis supertype_above: closest_common_supertype_is_above_both env declared.

Let of_fragment (t: EType): Prop := gfrag env t = true /\ refs_wf env declared t.

Lemma in_fragment_refs_wf: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> refs_wf env declared t)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> refs_wf env declared a).
Proof.
    induction k as [|k [IHt IHa]].
    { split; [intros [m c args|[m c args| | | | | |]| | | | |] Hd H|intros [| | | |v o n| |] Hd H]; simpl in Hd, H;
          try discriminate H; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        refs_wf env declared (RootResolved m c args)).
    { intros m c args Hd H. destruct (root_in_fragment env m c args H) as [_ Ha]. apply refs_wf_make_root.
      intros a Hin. pose proof (argument_depth_below m c args a Hin). apply IHa; [lia|apply Ha, Hin]. }
    split.
    - intros t Hd H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H1]]]]].
      + exact (Hroot m c args Hd H).
      + rewrite depth_nullable in Hd. exact (Hroot m c args ltac:(lia) H1).
    - intros [| | | |v o n| |] Hd H; simpl in H; try discriminate H. simpl in Hd |- *. apply IHt; [lia|exact H].
Qed.

Lemma in_fragment_of_fragment: forall t, in_fragment env t = true -> of_fragment t.
Proof.
    intros t H. split; [exact (in_fragment_is_gfrag env t H)|]. apply (proj1 (in_fragment_refs_wf (depth t))); [lia|exact H].
Qed.

(* Where unify terminates, it accepts what it never rejects *)
Lemma accepts: forall x y, of_fragment x -> of_fragment y ->
    never_fails env y x -> exists n, unify env n y x (Ongoing []) = Some (Ongoing []).
Proof.
    intros x y [Hx Hrx] [Hy Hry] Hnf.
    destruct (terminates env declared wf declared_wf finite not_expansive
        y x [] Hy Hx Hry Hrx) as [n Hn].
    exists n. specialize (Hnf n []).
    destruct (unify env n y x (Ongoing [])) as [[u|]|] eqn:E; [|contradiction Hnf; reflexivity|contradiction Hn; reflexivity].
    rewrite (gkeeps env wf n y x [] u Hy Hx E). reflexivity.
Qed.

Lemma reflexive: forall x, of_fragment x -> exists n, unify env n x x (Ongoing []) = Some (Ongoing []).
Proof.
    intros x Hx. apply accepts; [exact Hx|exact Hx|].
    apply reflexive_never_fails; [exact wf|apply Hx].
Qed.

Lemma assignable_unify: forall n x y, gfrag env x = true -> gfrag env y = true ->
    is_assignable_to env n x y = Some true -> unify env n y x (Ongoing []) = Some (Ongoing []).
Proof.
    intros n x y Hx Hy H. unfold is_assignable_to, empty_unification in H.
    destruct (unify env n y x (Ongoing [])) as [[u|]|] eqn:E; simpl in H; try discriminate H.
    rewrite (gkeeps env wf n y x [] u Hy Hx E). reflexivity.
Qed.

Lemma unify_assignable: forall n x y, unify env n y x (Ongoing []) = Some (Ongoing []) -> is_assignable_to env n x y = Some true.
Proof. intros n x y H. unfold is_assignable_to, empty_unification. rewrite H. reflexivity. Qed.

Let transitive := transitivity_terminating env wf declared declared_wf
    terminates finite not_expansive.

(* What is assignable to the intersection of a bound and a type is assignable to each of them *)
Lemma below_intersection: forall a b x n, of_fragment a -> in_fragment env b = true -> of_fragment x ->
    unify env n (intersect env a b) x (Ongoing []) = Some (Ongoing []) ->
    (exists n1, unify env n1 a x (Ongoing []) = Some (Ongoing [])) /\ (exists n1, unify env n1 b x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros a b x n Ha HB Hx H. pose proof (in_fragment_of_fragment b HB) as Hb.
    destruct (intersect_in_fragment a b Ha Hb) as [Hi Hri]. destruct (intersect_below a b Ha Hb) as [[na Hna] [nb Hnb]].
    apply unify_assignable in H.
    destruct (transitive n na x _ a (proj1 Hx) Hi (proj1 Ha) (proj2 Hx) Hri (proj2 Ha) H Hna) as [fa Ea].
    destruct (transitive n nb x _ b (proj1 Hx) Hi (proj1 Hb) (proj2 Hx) Hri (proj2 Hb) H Hnb) as [fb Eb].
    split; [exists fa; exact (assignable_unify fa x a (proj1 Hx) (proj1 Ha) Ea)|exists fb; exact (assignable_unify fb x b (proj1 Hx) (proj1 Hb) Eb)].
Qed.

(* What the closest common supertype of a bound and a type is assignable to, each of them is assignable to *)
Lemma above_supertype: forall a b x n, of_fragment a -> in_fragment env b = true -> of_fragment x ->
    unify env n x (closest_common_supertype_with env a b) (Ongoing []) = Some (Ongoing []) ->
    (exists n1, unify env n1 x a (Ongoing []) = Some (Ongoing [])) /\ (exists n1, unify env n1 x b (Ongoing []) = Some (Ongoing [])).
Proof.
    intros a b x n Ha HB Hx H. pose proof (in_fragment_of_fragment b HB) as Hb.
    destruct (supertype_in_fragment a b Ha Hb) as [Hs Hrs]. destruct (supertype_above a b Ha Hb) as [[na Hna] [nb Hnb]].
    apply unify_assignable in H.
    destruct (transitive na n a _ x (proj1 Ha) Hs (proj1 Hx) (proj2 Ha) Hrs (proj2 Hx) Hna H) as [fa Ea].
    destruct (transitive nb n b _ x (proj1 Hb) Hs (proj1 Hx) (proj2 Hb) Hrs (proj2 Hx) Hnb H) as [fb Eb].
    split; [exists fa; exact (assignable_unify fa a x (proj1 Ha) (proj1 Hx) Ea)|exists fb; exact (assignable_unify fb b x (proj1 Hb) (proj1 Hx) Eb)].
Qed.

(*
 * Calling a member function is sound, whatever the final values of its type parameters are: as in
 * Constraints.member_call_through_subtypes_sound, without assuming them types of the fragment of
 * Transitivity.v. They are of the fragment of Fragment.v (type parameters and intersections), given
 * the conjectures about intersect and closestCommonSupertypeWith, and that unify terminates where
 * inheritance isn't expansive.
 *)
Theorem member_call_with_any_final_values_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is; its type arguments as those of c are exact, and within the bounds *)
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx Hzb
        HPs HAs Hfold.
    exact (member_call_through_subtypes_sound env wf
        of_fragment (fun x H => proj1 H) in_fragment_of_fragment reflexive
        of_fragment in_fragment_of_fragment
        (fun a b Ha Hb => intersect_in_fragment a b Ha (in_fragment_of_fragment b Hb))
        (fun a b Ha Hb => supertype_in_fragment a b Ha (in_fragment_of_fragment b Hb))
        below_intersection above_supertype intersect_no_vars supertype_no_vars
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx Hzb
        HPs HAs Hfold (fun _ _ _ H => H)).
Qed.

End FinalValues.

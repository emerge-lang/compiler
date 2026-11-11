From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import GenericArguments.
From EmergeTypeSystem Require Import MemberAccess.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Members typed as intersections                                                                 *)
(*                                                                                                *)
(* MemberAccess.v, for members whose declared type is an intersection, made nullable or not, of    *)
(* components as MemberAccess.member_component has them: `A & T`, `(A & T!)?`, `A? & T`,           *)
(* `Box<out T> & mut T`. Through the object, the instance is the intersection of class types. Through *)
(* the reference, a component may be a type argument, a type parameter bound to one, and then the  *)
(* intersection is one (Subtyping.intersect_instances, as intersectMappedComponents makes it): out- *)
(* variant where any component is, the in-variant ones left out; in-variant where only those are.  *)
(* Read through an out-variant one, it is the intersection of the types of the components that   *)
(* aren't in-variant; through an in-variant one, `read Any?`. Written, an out-variant one takes    *)
(* nothing (or null, made nullable); an in-variant one what each of the types of the components    *)
(* takes. Both are sound: what the object holds is below what is read (intersection_member_read_sound), *)
(* and what is written is below what the object holds (intersection_member_write_sound).          *)
(*                                                                                                *)
(* Intersections aren't of the fragment of MemberAccess.v but of Fragment.v, where assignability   *)
(* rests on unify_terminates_on, as in GenericArguments.v.                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section MemberIntersections.

Variable env: Environment.
Hypothesis wf: wellformed env.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

(* The conjectures of Conjectures.v *)
Hypothesis terminates: unify_terminates_on env declared.

Let frag := of_fragment env declared.

Lemma frag_class: forall t, in_fragment env t = true -> frag t.
Proof. intros t H. split; [exact (in_fragment_is_gfrag env t H)|exact I]. Qed.

Lemma below_class: forall n x y, unify env n y x (Ongoing []) = Some (Ongoing []) -> below env x y.
Proof. intros n x y H. exists n. exact H. Qed.

Lemma trans: forall x y z, frag x -> frag y -> frag z -> below env x y -> below env y z -> below env x z.
Proof. exact (below_trans env wf declared declared_wf terminates ). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Intersections of class types                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* The intersection ofComponents makes of class types *)
Definition oc (l: list EType): EType := of_components env (flat_map intersected_components l).

Lemma intersected_class: forall t, in_fragment env t = true -> intersected_components t = [t].
Proof. intros t H. destruct (fragment_cases env t H) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; reflexivity. Qed.

Lemma flat_map_class: forall xs, (forall y, In y xs -> in_fragment env y = true) -> flat_map intersected_components xs = xs.
Proof.
    induction xs as [|y xs IH]; intros H; [reflexivity|]. cbn [flat_map].
    rewrite (intersected_class y (H y (or_introl eq_refl))), IH by (intros y' Hy'; apply H; right; exact Hy'). reflexivity.
Qed.

Lemma oc_single: forall y, in_fragment env y = true -> oc [y] = y.
Proof. intros y H. unfold oc. rewrite (flat_map_class [y]) by (intros y' [<-|[]]; exact H). reflexivity. Qed.

(* A class type of a mutability it is assigned as no less than is below it *)
Lemma remut_below: forall m x, in_fragment env x = true -> Model.is_subtype_of m (assignment_mutability env x) = true ->
    below env (with_mutability env m x) x.
Proof.
    intros m x Hw Hk. destruct (below_refl env wf declared declared_wf terminates x (frag_class x Hw)) as [f Hf].
    exists f. apply (unify_remut env f x x x _ [] [] (remut_refl env x Hw) (remut_with_mutability env m x Hw)); [|exact Hf].
    destruct (fit_cases env m x Hw) as [[E _]|[E _]]; rewrite E; [exact Hk|apply own_fits].
Qed.

Lemma without_null_below: forall x, in_fragment env x = true -> below env (without_null env x) x.
Proof.
    intros x Hw. destruct (below_refl env wf declared declared_wf terminates x (frag_class x Hw)) as [f Hf].
    exists f. exact (unify_without_null_assignee env f x x [] [] Hw Hw Hf).
Qed.

Lemma not_nullable_rewrap: forall t, (forall x, t <> Nullable x) -> rewrap_nullable t = Nullable t.
Proof. intros [| x | | | | |] H; try reflexivity. exfalso. exact (H x eq_refl). Qed.

(* Of class types none of which is nullable: their intersection, of the fragment, not nullable,
   below each of them *)
Lemma oc_nonnull: forall xs, xs <> [] -> (forall y, In y xs -> in_fragment env y = true /\ is_nullable env y = false) ->
    frag (oc xs) /\ is_nullable env (oc xs) = false /\ (forall y, In y xs -> below env (oc xs) y)
    /\ (forall x, oc xs <> Nullable x) /\ nullable_assignee env (oc xs) = oc xs.
Proof.
    intros xs Hne H.
    destruct xs as [|y1 [|y2 rest]]; [contradiction| |].
    - destruct (H y1 (or_introl eq_refl)) as [Hf Hn]. rewrite (oc_single y1 Hf).
      split; [exact (frag_class y1 Hf)|]. split; [exact Hn|].
      split; [intros y [<-|[]]; exact (below_refl env wf declared declared_wf terminates y1 (frag_class y1 Hf))|].
      destruct (fragment_cases env y1 Hf) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; [|discriminate Hn].
      split; [intros ? E; discriminate E|reflexivity].
    - set (xs := y1 :: y2 :: rest) in *.
      assert (Hl: 2 <= length xs) by (simpl; lia).
      assert (Hfr: frag (oc xs)).
      { destruct (below_of_components env wf declared declared_wf terminates bottom_type xs
            (bottom_of_fragment env wf declared) eq_refl Hl) as [_ [_ [Hf _]]].
        - intros y Hy. split; [exact (frag_class y (proj1 (H y Hy)))|].
          exact (below_bottom env wf declared declared_wf terminates y (frag_class y (proj1 (H y Hy)))).
        - apply Hf. intros y Hy Hny. rewrite (proj2 (H y Hy)) in Hny. discriminate Hny. }
      assert (E: oc xs = Intersection (map (fun c => with_mutability env (common_mutability env xs) (without_null env c)) xs)).
      { unfold oc. rewrite (flat_map_class xs) by (intros y Hy; exact (proj1 (H y Hy))).
        apply (of_components_many env xs Hl). unfold xs. cbn [forallb]. rewrite (proj2 (H y1 (or_introl eq_refl))). reflexivity. }
      assert (Hnl: is_nullable env (oc xs) = false).
      { rewrite E. cbn [is_nullable]. unfold xs. cbn [map forallb].
        destruct (H y1 (or_introl eq_refl)) as [Hf1 Hn1].
        rewrite (nullable_with_mutability env _ _ (in_fragment_without_null env y1 Hf1)),
            (Substitution.without_null_not_nullable env y1 Hf1). reflexivity. }
      split; [exact Hfr|]. split; [exact Hnl|].
      split; [|rewrite E in Hnl |- *; split; [intros x E'; discriminate E'|cbn [nullable_assignee]; exact (without_null_unchanged env _ Hnl)]].
      intros y Hy. destruct (H y Hy) as [Hf Hn].
      set (k := common_mutability env xs).
      assert (Hk: Model.is_subtype_of k (assignment_mutability env y) = true)
          by (exact (fold_intersect_below_element (map (assignment_mutability env) xs) readonly _ (in_map _ _ _ Hy))).
      pose proof (in_fragment_without_null env y Hf) as Hwf.
      assert (Hz: below env (oc xs) (with_mutability env k (without_null env y))).
      { rewrite E in Hfr |- *. apply (intersection_below_component env wf declared declared_wf terminates _ _ Hfr).
        apply in_map_iff. exists y. split; [reflexivity|exact Hy]. }
      assert (Hwm: frag (with_mutability env k (without_null env y))) by (apply frag_class, in_fragment_with_mutability, Hwf).
      apply (trans _ _ y Hfr Hwm (frag_class y Hf) Hz).
      apply (trans _ (without_null env y) y Hwm (frag_class _ Hwf) (frag_class y Hf)); [|exact (without_null_below y Hf)].
      apply (remut_below k _ Hwf). rewrite (assignment_mutability_of_without_null env y Hf). exact Hk.
Qed.

(* Of class types, the intersection is that of them without null, made nullable where all of them are *)
Lemma oc_split: forall xs, xs <> [] -> (forall y, In y xs -> in_fragment env y = true) ->
    oc xs = if forallb (is_nullable env) xs then Nullable (oc (map (without_null env) xs)) else oc (map (without_null env) xs).
Proof.
    intros xs Hne H.
    assert (Hw: forall y, In y (map (without_null env) xs) -> in_fragment env y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. exact (in_fragment_without_null env y' (H y' Hy')). }
    destruct xs as [|y1 [|y2 rest]]; [contradiction| |].
    - pose proof (H y1 (or_introl eq_refl)) as Hf. cbn [map forallb]. rewrite andb_true_r.
      rewrite (oc_single y1 Hf), (oc_single _ (in_fragment_without_null env y1 Hf)).
      destruct (fragment_cases env y1 Hf) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; reflexivity.
    - set (xs := y1 :: y2 :: rest) in *.
      assert (Hl: 2 <= length xs) by (simpl; lia).
      assert (Hcm: common_mutability env (map (without_null env) xs) = common_mutability env xs).
      { unfold common_mutability. rewrite map_map. f_equal. apply map_ext_in. intros y Hy.
        exact (assignment_mutability_of_without_null env y (H y Hy)). }
      assert (Ew: oc (map (without_null env) xs)
          = Intersection (map (fun c => with_mutability env (common_mutability env xs) (without_null env c)) xs)).
      { unfold oc. rewrite (flat_map_class _ Hw).
        rewrite (of_components_many env (map (without_null env) xs)); [|rewrite length_map; exact Hl|].
        - rewrite Hcm, map_map. f_equal. apply map_ext_in. intros y Hy. rewrite (without_null_idempotent env y (H y Hy)). reflexivity.
        - unfold xs. cbn [map forallb]. rewrite (Substitution.without_null_not_nullable env y1 (H y1 (or_introl eq_refl))). reflexivity. }
      rewrite Ew. unfold oc. rewrite (flat_map_class xs H).
      destruct (forallb (is_nullable env) xs) eqn:En.
      + assert (Ent: forallb is_nullable_type xs = true).
        { apply forallb_forall. intros y Hy. pose proof (proj1 (forallb_forall _ xs) En y Hy) as Hny.
          destruct (fragment_cases env y (H y Hy)) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; [discriminate Hny|reflexivity]. }
        unfold xs. unfold of_components. fold xs. rewrite En, Ent. reflexivity.
      + exact (of_components_many env xs Hl En).
Qed.

Lemma oc_without_null: forall xs, xs <> [] -> (forall y, In y xs -> in_fragment env y = true) ->
    map (without_null env) xs <> [] /\ forall y, In y (map (without_null env) xs) -> in_fragment env y = true /\ is_nullable env y = false.
Proof.
    intros xs Hne H. split; [destruct xs; [contradiction|discriminate]|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']].
    exact (conj (in_fragment_without_null env y' (H y' Hy')) (Substitution.without_null_not_nullable env y' (H y' Hy'))).
Qed.

(* The intersection of class types, made nullable or not, is of the fragment *)
Lemma oc_frag: forall xs, xs <> [] -> (forall y, In y xs -> in_fragment env y = true) ->
    frag (oc xs) /\ frag (rewrap_nullable (oc xs)) /\ rewrap_nullable (oc xs) = Nullable (oc (map (without_null env) xs)).
Proof.
    intros xs Hne H. destruct (oc_without_null xs Hne H) as [Hne' Hw].
    destruct (oc_nonnull _ Hne' Hw) as [Hf [Hn [_ [HN _]]]].
    pose proof (of_fragment_rewrap_not_nullable env declared _ Hf Hn) as Hr. rewrite (not_nullable_rewrap _ HN) in Hr.
    rewrite (oc_split xs Hne H). destruct (forallb (is_nullable env) xs).
    - split; [exact Hr|]. split; [exact Hr|reflexivity].
    - split; [exact Hf|]. rewrite (not_nullable_rewrap _ HN). split; [exact Hr|reflexivity].
Qed.

(* Where each of some class types is above one of others, the intersection of those is above that of
   the others, made nullable or not *)
Lemma classes_mono: forall xs ys, xs <> [] -> ys <> [] ->
    (forall x, In x xs -> in_fragment env x = true) -> (forall y, In y ys -> in_fragment env y = true) ->
    (forall y, In y ys -> exists x, In x xs /\ below env x y) ->
    below env (oc xs) (oc ys) /\ below env (rewrap_nullable (oc xs)) (rewrap_nullable (oc ys)).
Proof.
    intros xs ys Hxne Hyne Hxs Hys H.
    destruct (oc_without_null xs Hxne Hxs) as [Hxne' Hxw]. destruct (oc_without_null ys Hyne Hys) as [Hyne' Hyw].
    set (NX := oc (map (without_null env) xs)) in *. set (NY := oc (map (without_null env) ys)) in *.
    destruct (oc_nonnull _ Hxne' Hxw) as [HfX [HnX [HbX [HNX HaX]]]].
    destruct (oc_nonnull _ Hyne' Hyw) as [HfY [HnY [_ [HNY _]]]].
    fold NX in HfX, HnX, HbX, HNX, HaX. fold NY in HfY, HnY, HNY.
    (* without null, the one is below the other *)
    assert (Hcore: below env NX NY).
    { assert (Hy: forall y, In y (map (without_null env) ys) -> below env NX y).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [y0 [<- Hy0]]. destruct (H y0 Hy0) as [x [Hx [f Hf]]].
        apply (trans _ (without_null env x) _ HfX (frag_class _ (proj1 (Hxw _ (in_map _ _ _ Hx))))
            (frag_class _ (proj1 (Hyw _ (in_map _ _ _ Hy0))))); [exact (HbX _ (in_map _ _ _ Hx))|].
        exists f. exact (unify_without_null env f y0 x [] [] (Hys y0 Hy0) (Hxs x Hx) Hf). }
      unfold NY. destruct ys as [|y1 [|y2 rest]]; [contradiction| |].
      - cbn [map]. rewrite (oc_single _ (proj1 (Hyw _ (or_introl eq_refl)))). exact (Hy _ (or_introl eq_refl)).
      - refine (proj1 (below_of_components env wf declared declared_wf terminates NX
            (map (without_null env) (y1 :: y2 :: rest)) HfX HnX ltac:(simpl; lia) _)).
        intros y Hy'. split; [exact (frag_class y (proj1 (Hyw y Hy')))|exact (Hy y Hy')]. }
    assert (HrY: frag (Nullable NY)).
    { pose proof (of_fragment_rewrap_not_nullable env declared _ HfY HnY) as Hr. rewrite (not_nullable_rewrap _ HNY) in Hr. exact Hr. }
    assert (Hnn: below env (Nullable NX) (Nullable NY)).
    { pose proof (nullable_assigned_below env NY NX (proj1 HrY) Hcore) as Hb. rewrite (not_nullable_rewrap _ HNX) in Hb. exact Hb. }
    rewrite (oc_split xs Hxne Hxs), (oc_split ys Hyne Hys). fold NX NY.
    destruct (forallb (is_nullable env) xs) eqn:Ex.
    - (* all of the ones below nullable: so are those above *)
      assert (Ey: forallb (is_nullable env) ys = true).
      { apply forallb_forall. intros y Hy. destruct (H y Hy) as [x [Hx [f Hf]]].
        destruct (is_nullable env y) eqn:Eny; [reflexivity|].
        pose proof (accepted_non_null env f y x [] [] (Hys y Hy) (Hxs x Hx) Eny Hf) as Enx.
        rewrite (proj1 (forallb_forall _ xs) Ex x Hx) in Enx. discriminate Enx. }
      rewrite Ey. cbn [rewrap_nullable]. split; exact Hnn.
    - rewrite (not_nullable_rewrap _ HNX).
      split; [|destruct (forallb (is_nullable env) ys); [exact Hnn|rewrite (not_nullable_rewrap _ HNY); exact Hnn]].
      destruct (forallb (is_nullable env) ys); [|exact Hcore].
      pose proof (nullable_below env wf declared declared_wf NX NY (proj1 HfX) ltac:(rewrite HaX; exact Hcore)) as Hb.
      rewrite (not_nullable_rewrap _ HNY) in Hb. exact Hb.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The instances of the components through the reference                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* A type in the instance of an intersection, read: a component that isn't a type argument, or the
   type of one that isn't in-variant *)
Definition readable (L: list EType) (k: EType): Prop :=
    exists t, In t L /\ ((not_argument t = true /\ k = t) \/ exists v o, t = TypeArgument v o k /\ v <> input).

(* None of them out-variant: what is written is of each of their types *)
Definition none_out (L: list EType): Prop := forall t v o x, In t L -> t = TypeArgument v o x -> v <> output.

Lemma filter_all: forall (Q: EType -> bool) xs, (forall t, Q t = true) -> filter Q xs = xs.
Proof. intros Q xs H. induction xs as [|t xs IH]; [reflexivity|]. simpl. rewrite H, IH. reflexivity. Qed.

Lemma argument_of_variance: forall v0 v1 o x, is_argument_of v0 (TypeArgument v1 o x) = false -> v1 <> v0.
Proof. intros v0 v1 o x H E. subst. unfold is_argument_of in H. destruct v0; discriminate H. Qed.

Lemma no_argument_of: forall v0 xs, existsb (is_argument_of v0) xs = false ->
    forall t v1 o x, In t xs -> t = TypeArgument v1 o x -> v1 <> v0.
Proof.
    intros v0 xs E t v1 o x Ht ->. apply argument_of_variance with (o := o) (x := x).
    destruct (is_argument_of v0 (TypeArgument v1 o x)) eqn:E'; [|reflexivity].
    rewrite (proj2 (existsb_exists _ xs) (ex_intro _ _ (conj Ht E'))) in E. discriminate E.
Qed.

Lemma unwrap_readable: forall xs, (forall t v o x, In t xs -> t = TypeArgument v o x -> v <> input) ->
    forall y, In y (map unwrap_argument xs) -> readable xs y.
Proof.
    intros xs H y Hk. apply in_map_iff in Hk. destruct Hk as [t [<- Ht]]. exists t. split; [exact Ht|].
    destruct t as [| | | |v o x| |]; try (left; split; reflexivity).
    right. exists v, o. split; [reflexivity|exact (H _ v o x Ht eq_refl)].
Qed.

Lemma unwrap_plain: forall xs, (forall t, In t xs -> not_argument t = true) -> map unwrap_argument xs = xs.
Proof.
    induction xs as [|t xs IH]; intros H; [reflexivity|]. cbn [map]. rewrite IH by (intros t' Ht'; apply H; right; exact Ht').
    pose proof (H t (or_introl eq_refl)) as Ht. destruct t; first [reflexivity|discriminate Ht].
Qed.

(* The intersection of the instances of the components (intersectMappedComponents) *)
Lemma instance_cases: forall xs, xs <> [] ->
    (intersect_instances env xs = oc xs /\ forall t, In t xs -> not_argument t = true)
    \/ (exists ys, intersect_instances env xs = TypeArgument output any_ownership (oc ys) /\ ys <> [] /\ forall y, In y ys -> readable xs y)
    \/ (intersect_instances env xs = TypeArgument input any_ownership (oc (map unwrap_argument xs)) /\ none_out xs)
    \/ (intersect_instances env xs = oc (map unwrap_argument xs) /\ none_out xs
        /\ forall t v o x, In t xs -> t = TypeArgument v o x -> v <> input).
Proof.
    intros xs Hne. unfold intersect_instances. destruct (existsb _ xs) eqn:Ea.
    2:{ left. split; [reflexivity|]. intros t Ht. destruct t; try reflexivity.
        exfalso. rewrite (proj2 (existsb_exists _ xs) (ex_intro _ _ (conj Ht eq_refl))) in Ea. discriminate Ea. }
    destruct (existsb (is_argument_of output) xs) eqn:Eo.
    - right. left. eexists. split; [reflexivity|]. split.
      + apply existsb_exists in Eo. destruct Eo as [t [Ht Et]].
        assert (Hin: In t (filter (fun t => negb (Variance_beq output output && is_argument_of input t)) xs)).
        { apply filter_In. split; [exact Ht|]. destruct t as [| | | |[] o x| |]; try discriminate Et; reflexivity. }
        intros E. apply (in_map unwrap_argument) in Hin. rewrite E in Hin. exact Hin.
      + intros y Hk. apply in_map_iff in Hk. destruct Hk as [t [<- Ht]]. apply filter_In in Ht. destruct Ht as [Ht Ef].
        exists t. split; [exact Ht|]. destruct t as [| | | |v o x| |]; try (left; split; reflexivity).
        right. exists v, o. split; [reflexivity|]. cbn [Variance_beq andb negb] in Ef.
        apply argument_of_variance with (o := o) (x := x). destruct (is_argument_of input _); [discriminate Ef|reflexivity].
    - pose proof (no_argument_of output xs Eo) as Hno.
      destruct (existsb (is_argument_of input) xs) eqn:Ei.
      + right. right. left. rewrite filter_all by (intros t; reflexivity). split; [reflexivity|exact Hno].
      + right. right. right. rewrite filter_all by (intros t; reflexivity).
        split; [reflexivity|]. split; [exact Hno|exact (no_argument_of input xs Ei)].
Qed.

(* What read_member reads of an instance *)
Definition read_of (t: EType): EType :=
    match t with
    | TypeArgument v _ x => read_type v x
    | Nullable (TypeArgument v _ x) => rewrap_nullable (read_type v x)
    | t => t
    end.

Lemma read_member_of: forall b V, read_member env b V = read_of (instantiate env b V).
Proof. intros b V. unfold read_member, read_of. destruct (instantiate env b V) as [| [] | | | | |]; reflexivity. Qed.

Lemma read_of_gfrag: forall t, gfrag env t = true -> read_of t = t.
Proof.
    intros t H. destruct (gfrag_cases env t H) as [[? [? [? ->]]]|[[n [-> [_ Hn]]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; try reflexivity.
    destruct n; try reflexivity. discriminate Hn.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Instances.

Variables (n': nat) (c: Class) (xs ys cs: list EType).
Hypothesis Hlx: length xs = length (parameter_ids env c).
Hypothesis Hly: length ys = length (parameter_ids env c).
Hypothesis Hxs: forall x, In x xs -> is_exact_argument env x = true.
Hypothesis Hys: forall y, In y ys -> argument_in_fragment env y = true.
Hypothesis Hpairs: Forall2 (fun x y => unify env n' y x (Ongoing []) = Some (Ongoing [])) xs ys.
Hypothesis Hcs: 2 <= length cs.
Hypothesis HC: forall C, In C cs -> member_component env c C = true.

Let LX := map (instantiate env (bindings_of env c xs)) cs.
Let LY := map (instantiate env (bindings_of env c ys)) cs.

Let CI C (H: In C cs) := component_instances env wf n' [] c xs ys C Hlx Hly Hxs Hys Hpairs (HC C H).

Lemma LX_facts: LX <> [] /\ forall x, In x LX -> in_fragment env x = true /\ not_argument x = true.
Proof.
    split; [unfold LX; destruct cs; [simpl in Hcs; lia|discriminate]|].
    intros x Hx. unfold LX in Hx. apply in_map_iff in Hx. destruct Hx as [C [<- HinC]].
    destruct (CI C HinC) as [Hf [Hn _]]. exact (conj Hf Hn).
Qed.

Lemma LY_nonempty: LY <> [].
Proof. unfold LY. destruct cs; [simpl in Hcs; lia|discriminate]. Qed.

Lemma object_instance: instantiate env (bindings_of env c xs) (Intersection cs) = oc LX.
Proof.
    change (instantiate env (bindings_of env c xs) (Intersection cs)) with (intersect_instances env LX).
    apply intersect_instances_plain. intros x Hx. exact (proj2 (proj2 LX_facts x Hx)).
Qed.

(* The types read through the reference are above those through the object *)
Lemma readable_above: forall zs, zs <> [] -> (forall y, In y zs -> readable LY y) ->
    below env (oc LX) (oc zs) /\ below env (rewrap_nullable (oc LX)) (rewrap_nullable (oc zs)).
Proof.
    intros zs Hne HK. destruct LX_facts as [HXne HX].
    apply (classes_mono LX zs HXne Hne (fun x Hx => proj1 (HX x Hx))).
    - intros y Hk. destruct (HK y Hk) as [t [Ht Hkt]]. unfold LY in Ht. apply in_map_iff in Ht. destruct Ht as [C [Et HinC]].
      destruct (CI C HinC) as [_ [_ [[HfY [HnY _]]|[v [o [Y [EY [HY _]]]]]]]]; rewrite Et in *.
      + destruct Hkt as [[_ ->]|[v [o [E _]]]]; [exact HfY|]. rewrite E in HnY. discriminate HnY.
      + destruct Hkt as [[Hn _]|[v' [o' [E _]]]]; [rewrite EY in Hn; discriminate Hn|]. rewrite EY in E. injection E as _ _ ->. exact HY.
    - intros y Hk. destruct (HK y Hk) as [t [Ht Hkt]]. unfold LY in Ht. apply in_map_iff in Ht. destruct Ht as [C [Et HinC]].
      exists (instantiate env (bindings_of env c xs) C). split; [apply in_map, HinC|].
      destruct (CI C HinC) as [_ [_ [[_ [HnY [[f Hf] _]]]|[v [o [Y [EY [_ [Hup _]]]]]]]]]; rewrite Et in *.
      + destruct Hkt as [[_ ->]|[v [o [E _]]]]; [exists f; exact Hf|]. rewrite E in HnY. discriminate HnY.
      + destruct Hkt as [[Hn _]|[v' [o' [E Hv]]]]; [rewrite EY in Hn; discriminate Hn|].
        rewrite EY in E. injection E as -> -> ->. destruct (Hup Hv) as [f Hf]. exists f. exact Hf.
Qed.

(* The types written through the reference, none of them out-variant, are below those through the
   object, where the reference doesn't widen them *)
Lemma written_below: mentions_loosely_bound_in_arguments (bindings_of env c ys) (Intersection cs) = false -> none_out LY ->
    below env (oc (map unwrap_argument LY)) (oc LX)
    /\ below env (rewrap_nullable (oc (map unwrap_argument LY))) (rewrap_nullable (oc LX)).
Proof.
    intros Hm Hno. destruct LX_facts as [HXne HX].
    assert (Hmc: forall C, In C cs -> mentions_loosely_bound_in_arguments (bindings_of env c ys) C = false).
    { intros C HinC. cbn [mentions_loosely_bound_in_arguments] in Hm. destruct (mentions_loosely_bound_in_arguments (bindings_of env c ys) C) eqn:E; [|reflexivity].
      rewrite (proj2 (existsb_exists _ cs) (ex_intro _ C (conj HinC E))) in Hm. discriminate Hm. }
    assert (Hne: map unwrap_argument LY <> []) by (pose proof LY_nonempty as H; destruct LY; [contradiction|discriminate]).
    apply (classes_mono _ LX Hne HXne).
    - intros k Hk. apply in_map_iff in Hk. destruct Hk as [t [<- Ht]]. unfold LY in Ht. apply in_map_iff in Ht. destruct Ht as [C [<- HinC]].
      destruct (CI C HinC) as [_ [_ [[HfY [HnY _]]|[v [o [Y [EY [HY _]]]]]]]].
      + destruct (instantiate env (bindings_of env c ys) C); first [exact HfY|discriminate HnY].
      + rewrite EY. exact HY.
    - intros x Hx. exact (proj1 (HX x Hx)).
    - intros x Hx. unfold LX in Hx. apply in_map_iff in Hx. destruct Hx as [C [<- HinC]].
      assert (HtL: In (instantiate env (bindings_of env c ys) C) LY) by (apply in_map, HinC).
      exists (unwrap_argument (instantiate env (bindings_of env c ys) C)). split; [apply in_map, HtL|].
      destruct (CI C HinC) as [_ [_ [[_ [HnY [_ Hdown]]]|[v [o [Y [EY [_ [_ Hdown]]]]]]]]].
      + destruct (Hdown (Hmc C HinC)) as [f Hf]. exists f.
        destruct (instantiate env (bindings_of env c ys) C); first [exact Hf|discriminate HnY].
      + rewrite EY. destruct (Hdown (Hno _ v o Y HtL EY)) as [f Hf]. exists f. exact Hf.
Qed.


(* The instances through the reference: class types, or type arguments of class types *)
Lemma LY_types: forall t, In t LY ->
    (not_argument t = true /\ in_fragment env t = true) \/ exists v o y, t = TypeArgument v o y /\ in_fragment env y = true.
Proof.
    intros t Ht. unfold LY in Ht. apply in_map_iff in Ht. destruct Ht as [C [<- HinC]].
    destruct (CI C HinC) as [_ [_ [[HfY [HnY _]]|[v [o [y [EY [HY _]]]]]]]].
    - left. split; assumption.
    - right. exists v, o, y. split; assumption.
Qed.

Lemma readable_fragment: forall x, readable LY x -> in_fragment env x = true.
Proof.
    intros x [t [Ht [[Hn ->]|[v [o [-> _]]]]]]; destruct (LY_types _ Ht) as [[_ Hf]|[v' [o' [Y [E HY]]]]].
    - exact Hf.
    - rewrite E in Hn. discriminate Hn.
    - discriminate Hf.
    - injection E as _ _ ->. exact HY.
Qed.

Lemma unwrapped_fragment: forall x, In x (map unwrap_argument LY) -> in_fragment env x = true.
Proof.
    intros x Hk. apply in_map_iff in Hk. destruct Hk as [t [<- Ht]].
    destruct (LY_types t Ht) as [[Hn Hf]|[v [o [Y [-> HY]]]]]; [|exact HY].
    destruct t; first [exact Hf|discriminate Hn].
Qed.

Lemma unwrapped_nonempty: map unwrap_argument LY <> [].
Proof. pose proof LY_nonempty as H. destruct LY; [contradiction|discriminate]. Qed.

Lemma plain_fragment: (forall t, In t LY -> not_argument t = true) -> forall x, In x LY -> in_fragment env x = true.
Proof.
    intros Hna x Hk. apply unwrapped_fragment. rewrite (unwrap_plain LY Hna). exact Hk.
Qed.

Lemma plain_none_out: (forall t, In t LY -> not_argument t = true) -> none_out LY.
Proof. intros Hna t v o x Ht ->. specialize (Hna _ Ht). discriminate Hna. Qed.

(* Reading a member typed as an intersection, through the reference, reads no less than the object
   holds *)
Lemma read_intersection: forall V, V = Intersection cs \/ V = Nullable (Intersection cs) ->
    frag (instantiate env (bindings_of env c xs) V) /\ frag (read_member env (bindings_of env c ys) V)
    /\ below env (instantiate env (bindings_of env c xs) V) (read_member env (bindings_of env c ys) V).
Proof.
    intros V Hf. destruct LX_facts as [HXne HX].
    destruct (oc_frag LX HXne (fun x Hx => proj1 (HX x Hx))) as [HfX [HrX _]].
    rewrite read_member_of.
    assert (EY: instantiate env (bindings_of env c ys) (Intersection cs) = intersect_instances env LY) by reflexivity.
    assert (Hrd: forall K, K <> [] -> (forall k, In k K -> readable LY k) ->
        frag (oc K) /\ frag (rewrap_nullable (oc K)) /\ below env (oc LX) (oc K)
        /\ below env (rewrap_nullable (oc LX)) (rewrap_nullable (oc K))).
    { intros K Hne HK. destruct (oc_frag K Hne (fun k Hk => readable_fragment k (HK k Hk))) as [H1 [H2 _]].
      destruct (readable_above K Hne HK) as [H3 H4]. auto. }
    assert (Hplain: (forall t, In t LY -> not_argument t = true) -> forall k, In k LY -> readable LY k).
    { intros Hna k Hk. exists k. split; [exact Hk|left; split; [exact (Hna k Hk)|reflexivity]]. }
    destruct Hf as [-> | ->].
    - rewrite object_instance, EY. split; [exact HfX|].
      destruct (instance_cases LY LY_nonempty) as [[E Hna]|[[K [E [HKne HK]]]|[[E Hno]|[E [Hno Hni]]]]]; rewrite E.
      + destruct (Hrd LY LY_nonempty (Hplain Hna)) as [H1 [_ [H3 _]]]. rewrite (read_of_gfrag _ (proj1 H1)). auto.
      + destruct (Hrd K HKne HK) as [H1 [_ [H3 _]]]. cbn [read_of read_type]. auto.
      + cbn [read_of read_type]. split; [exact (top_of_fragment env wf declared)|].
        exact (below_top env wf declared declared_wf terminates _ HfX).
      + destruct (Hrd _ unwrapped_nonempty (unwrap_readable LY Hni)) as [H1 [_ [H3 _]]].
        rewrite (read_of_gfrag _ (proj1 H1)). auto.
    - change (instantiate env (bindings_of env c xs) (Nullable (Intersection cs)))
          with (rewrap_nullable (instantiate env (bindings_of env c xs) (Intersection cs))).
      change (instantiate env (bindings_of env c ys) (Nullable (Intersection cs)))
          with (rewrap_nullable (instantiate env (bindings_of env c ys) (Intersection cs))).
      rewrite object_instance, EY. split; [exact HrX|].
      destruct (instance_cases LY LY_nonempty) as [[E Hna]|[[K [E [HKne HK]]]|[[E Hno]|[E [Hno Hni]]]]]; rewrite E.
      + destruct (Hrd LY LY_nonempty (Hplain Hna)) as [_ [H2 [_ H4]]]. rewrite (read_of_gfrag _ (proj1 H2)). auto.
      + destruct (Hrd K HKne HK) as [_ [H2 [_ H4]]]. cbn [rewrap_nullable read_of read_type]. auto.
      + cbn [rewrap_nullable read_of read_type]. split; [exact (top_of_fragment env wf declared)|].
        exact (below_top env wf declared declared_wf terminates _ HrX).
      + destruct (Hrd _ unwrapped_nonempty (unwrap_readable LY Hni)) as [_ [H2 [_ H4]]].
        rewrite (read_of_gfrag _ (proj1 H2)). auto.
Qed.

(* Writing a member typed as an intersection, through the reference, writes no more than the object
   holds; or null, to a nullable one *)
Lemma write_intersection: forall y V fuel, y = Intersection cs \/ y = Nullable (Intersection cs) ->
    in_fragment env V = true -> is_non_nullable_nothing env V = false ->
    unify env fuel (write_member env (bindings_of env c ys) y) V (Ongoing []) = Some (Ongoing []) ->
    below env V (instantiate env (bindings_of env c xs) y)
    \/ (holds_only_null env V = true /\ is_nullable env (instantiate env (bindings_of env c xs) y) = true).
Proof.
    intros y V fuel Hf HV HVn HW. pose proof (frag_class V HV) as HfV. destruct LX_facts as [HXne HX].
    destruct (oc_frag LX HXne (fun x Hx => proj1 (HX x Hx))) as [HfX [HrX EX]].
    destruct (oc_frag _ unwrapped_nonempty unwrapped_fragment) as [HfT [HrT _]].
    assert (EY: instantiate env (bindings_of env c ys) (Intersection cs) = intersect_instances env LY) by reflexivity.
    unfold write_member in HW.
    replace (mentions_loosely_bound_in_arguments (bindings_of env c ys) y)
        with (mentions_loosely_bound_in_arguments (bindings_of env c ys) (Intersection cs)) in HW
        by (destruct Hf as [-> | ->]; reflexivity).
    destruct (mentions_loosely_bound_in_arguments (bindings_of env c ys) (Intersection cs)) eqn:Em.
    - (* nothing but Nothing, or null *)
      left. destruct Hf as [-> | ->]; cbn iota in HW.
      + rewrite object_instance. apply (trans V bottom_type _ HfV (bottom_of_fragment env wf declared) HfX); [exists fuel; exact HW|].
        exact (below_bottom env wf declared declared_wf terminates _ HfX).
      + change (instantiate env (bindings_of env c xs) (Nullable (Intersection cs)))
            with (rewrap_nullable (instantiate env (bindings_of env c xs) (Intersection cs))).
        rewrite object_instance.
        assert (HfN: frag (Nullable bottom_type))
            by exact (of_fragment_rewrap_not_nullable env declared _ (bottom_of_fragment env wf declared) eq_refl).
        apply (trans V (Nullable bottom_type) _ HfV HfN HrX); [exists fuel; exact HW|].
        destruct (oc_without_null LX HXne (fun x Hx => proj1 (HX x Hx))) as [Hne' Hw].
        destruct (oc_nonnull _ Hne' Hw) as [HfNX _].
        rewrite EX. rewrite EX in HrX.
        exact (nullable_assigned_below env _ bottom_type (proj1 HrX)
            (below_bottom env wf declared declared_wf terminates _ HfNX)).
    - pose proof (fun H => proj1 (written_below Em H)) as Hw1. pose proof (fun H => proj2 (written_below Em H)) as Hw2.
      destruct Hf as [-> | ->].
      + left. rewrite object_instance. rewrite EY in HW.
        destruct (instance_cases LY LY_nonempty) as [[E Hna]|[[K [E [HKne HK]]]|[[E Hno]|[E [Hno Hni]]]]]; rewrite E in HW.
        * rewrite <- (unwrap_plain LY Hna) in HW. specialize (Hw1 (plain_none_out Hna)).
          exact (trans V _ _ HfV HfT HfX (ex_intro _ fuel HW) Hw1).
        * exfalso. destruct fuel as [|fuel]; [discriminate HW|].
          rewrite (unify_argument_value env fuel output any_ownership _ V [] HV), HVn in HW. discriminate HW.
        * destruct fuel as [|fuel]; [discriminate HW|].
          rewrite (unify_argument_value env fuel input any_ownership _ V [] HV) in HW.
          exact (trans V _ _ HfV HfT HfX (ex_intro _ fuel HW) (Hw1 Hno)).
        * exact (trans V _ _ HfV HfT HfX (ex_intro _ fuel HW) (Hw1 Hno)).
      + change (instantiate env (bindings_of env c xs) (Nullable (Intersection cs)))
            with (rewrap_nullable (instantiate env (bindings_of env c xs) (Intersection cs))).
        change (instantiate env (bindings_of env c ys) (Nullable (Intersection cs)))
            with (rewrap_nullable (instantiate env (bindings_of env c ys) (Intersection cs))) in HW.
        rewrite object_instance. rewrite EY in HW.
        (* what is below a type argument made nullable, not out-variant, is below its type made nullable *)
        assert (Hin: forall v T, v <> output -> unify env fuel (Nullable (TypeArgument v any_ownership T)) V (Ongoing []) = Some (Ongoing []) ->
            frag T -> below env V (rewrap_nullable T)).
        { intros v T Hv E HT. destruct fuel as [|y]; [discriminate E|].
          rewrite (nullable_target env y _ V [] (proj1 HfV)) in E.
          destruct (nullable_assignee_facts env wf declared declared_wf V (proj1 HfV)) as [Hg _].
          destruct y as [|y]; [discriminate E|].
          apply (nullable_below env wf declared declared_wf V T (proj1 HfV)).
          refine (argument_value_below env wf declared declared_wf terminates y v any_ownership T _ _ HT (conj Hg I) E).
          destruct v; first [reflexivity|contradiction Hv; reflexivity]. }
        destruct (instance_cases LY LY_nonempty) as [[E Hna]|[[K [E [HKne HK]]]|[[E Hno]|[E [Hno Hni]]]]]; rewrite E in HW.
        * left. rewrite <- (unwrap_plain LY Hna) in HW. specialize (Hw2 (plain_none_out Hna)).
          exact (trans V _ _ HfV HrT HrX (ex_intro _ fuel HW) Hw2).
        * (* nothing but null *)
          cbn [rewrap_nullable] in HW. destruct fuel as [|fuel]; [discriminate HW|].
          destruct (fragment_cases env V HV) as [[mv [cv [vargs ->]]]|[mv [cv [vargs [-> HV']]]]].
          -- exfalso. rewrite unify_nullable_class in HW. destruct fuel as [|fuel]; [discriminate HW|].
             rewrite (unify_argument_value env fuel output any_ownership _ _ [] HV), HVn in HW. discriminate HW.
          -- rewrite unify_nullable_nullable in HW. destruct fuel as [|fuel]; [discriminate HW|].
             rewrite (unify_argument_value env fuel output any_ownership _ _ [] HV') in HW. cbn [Variance_beq] in HW.
             right. split; [|apply rewrap_is_nullable].
             cbn [holds_only_null]. destruct (is_non_nullable_nothing env (RootResolved mv cv vargs)); [reflexivity|discriminate HW].
        * left. cbn [rewrap_nullable] in HW.
          exact (trans V _ _ HfV HrT HrX (Hin input _ ltac:(discriminate) HW HfT) (Hw2 Hno)).
        * left. exact (trans V _ _ HfV HrT HrX (ex_intro _ fuel HW) (Hw2 Hno)).
Qed.

End Instances.


(* The declared type of a member: an intersection of components as MemberAccess.member_component has
   them, made nullable or not *)
Definition member_intersection (c: Class) (f: EType): Prop :=
    exists cs, (f = Intersection cs \/ f = Nullable (Intersection cs))
        /\ 2 <= length cs /\ forall C, In C cs -> member_component env c C = true.

(*
 * Reading a member typed as an intersection through a reference is sound: what the member of the
 * object holds is assignable to what is read through the reference.
 *)
Theorem intersection_member_read_sound: forall n m c xs m' ys z V,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument env x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing []) = Some (Ongoing []) ->
    member_intersection c z -> frag V ->
    below env V (read_member env (bindings_of env c xs) z) -> below env V (read_member env (bindings_of env c ys) z).
Proof.
    intros n m c xs m' ys z V Hc Hlx Hly Hxs Hys H [cs [Hf [Hcs HC]]] HV HVx.
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true)
        by (intros x Hx; destruct (exact_argument_facts env x (Hxs x Hx)) as [? [? [_ [_ [? _]]]]]; assumption).
    destruct (receiver_arguments env wf n [] m c xs m' ys Hc ltac:(lia) Hfxs Hys H) as [n' [-> Hpairs]].
    destruct (read_intersection n' c xs ys cs Hlx Hly Hxs Hys Hpairs Hcs HC z Hf) as [HfX [HfY Hb]].
    rewrite read_member_of, (read_of_gfrag _ (proj1 HfX)) in HVx.
    exact (trans V _ _ HV HfX HfY HVx Hb).
Qed.

(*
 * Writing a member typed as an intersection through a reference is sound: what is assignable to the
 * member through the reference is assignable to the member of the object; or null, to a nullable
 * member.
 *)
Theorem intersection_member_write_sound: forall n m c xs m' ys z V fuel,
    c <> nothing ->
    length xs = length (parameter_ids env c) -> length ys = length (parameter_ids env c) ->
    (forall x, In x xs -> is_exact_argument env x = true) -> (forall y, In y ys -> argument_in_fragment env y = true) ->
    unify env n (RootResolved m' c ys) (RootResolved m c xs) (Ongoing []) = Some (Ongoing []) ->
    member_intersection c z ->
    in_fragment env V = true -> is_non_nullable_nothing env V = false ->
    unify env fuel (write_member env (bindings_of env c ys) z) V (Ongoing []) = Some (Ongoing []) ->
    below env V (read_member env (bindings_of env c xs) z)
    \/ (holds_only_null env V = true /\ is_nullable env (read_member env (bindings_of env c xs) z) = true).
Proof.
    intros n m c xs m' ys z V fuel Hc Hlx Hly Hxs Hys H [cs [Hf [Hcs HC]]] HV HVn HW.
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true)
        by (intros x Hx; destruct (exact_argument_facts env x (Hxs x Hx)) as [? [? [_ [_ [? _]]]]]; assumption).
    destruct (receiver_arguments env wf n [] m c xs m' ys Hc ltac:(lia) Hfxs Hys H) as [n' [-> Hpairs]].
    destruct (read_intersection n' c xs ys cs Hlx Hly Hxs Hys Hpairs Hcs HC z Hf) as [HfX _].
    rewrite read_member_of, (read_of_gfrag _ (proj1 HfX)).
    exact (write_intersection n' c xs ys cs Hlx Hly Hxs Hys Hpairs Hcs HC z V fuel Hf HV HVn HW).
Qed.

End MemberIntersections.

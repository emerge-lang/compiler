From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import MemberAccess.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import FinalValues.
From EmergeTypeSystem Require Import SubstitutionTerminating.
From EmergeTypeSystem Require Import GenericArguments.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Substitution with intersections in type arguments                                              *)
(*                                                                                                *)
(* The substitution lemma of Substitution.v, for types whose type arguments may be intersections, *)
(* too (`Box<A & T>`, the wide fragment wtfrag). Instantiated, those are types of the fragment of *)
(* Fragment.v without type parameters (ground), but no longer of the fragment of Transitivity.v,  *)
(* whose transitivity Substitution.v relies on. So this takes transitivity from Generics.v and    *)
(* Conjectures.v: where unify terminates on the environment (unify_terminates_on, a premise about *)
(* the program at hand; Conjectures.v says what is known about which programs it holds for),      *)
(* unify is transitive on them (transitivity_terminating), and what it never                      *)
(* rejects, it accepts (accepts). The proof is the induction of Substitution.v once more, in the  *)
(* form of some fuel being enough (wide_main), with intersections as targets and as assignees in  *)
(* every position: an intersection takes what each of its components takes, of the mutability     *)
(* common to them; one is taken where one of its components is.                                   *)
(*                                                                                                *)
(* The types of generic code (ktfrag) are those, and intersections whose components keep their   *)
(* nullability (`A? & P` with `P : Any?`), nullable or not, at the top and in type arguments.     *)
(* Instantiated, such an intersection is ofComponents of class types, nullable or not: below each *)
(* of them, and above what is below each (of_components_below, below_of_components_ground). As    *)
(* the target, each of its components takes the assignee (wide_kept_target); as the assignee, one *)
(* of them is taken (wide_into_kept), or a nullable target takes it without null, an intersection *)
(* of the wide fragment (kept_without_null).                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Section Ground.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.

(* No references to type parameters, type variables or erroneous types in it *)
Fixpoint no_refs (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb no_refs arguments
    | Nullable n | TypeArgument _ _ n => no_refs n
    | Intersection components => forallb no_refs components
    | _ => false
    end.

(* What instantiating types gives: the types of Fragment.v without type parameters *)
Definition ground (t: EType): bool := gfrag env t && no_refs t.

Lemma ground_gfrag: forall t, ground t = true -> gfrag env t = true.
Proof. intros t H. apply andb_true_iff in H. apply H. Qed.

Lemma ground_no_vars: forall t, ground t = true -> no_vars t = true.
Proof. intros t H. exact (gfrag_no_vars env t (ground_gfrag t H)). Qed.

Lemma no_refs_refs_wf: forall t, no_refs t = true -> refs_wf env declared t.
Proof. intros. exact I. Qed.

Lemma ground_of_fragment: forall t, ground t = true -> gfrag env t = true /\ refs_wf env declared t.
Proof. intros t H. apply andb_true_iff in H. destruct H as [Hg Hn]. exact (conj Hg (no_refs_refs_wf t Hn)). Qed.

Lemma in_fragment_no_refs: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> no_refs t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> no_refs a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; [intros [m c args|[m c args| | | | | |]| | | | |] Hd H|intros [| | | |v o n| |] Hd H]; simpl in Hd, H;
          try discriminate H; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        no_refs (RootResolved m c args) = true).
    { intros m c args Hd H. destruct (root_in_fragment env m c args H) as [_ Ha].
      change (forallb no_refs args = true). apply forallb_forall.
      intros a Hin. pose proof (argument_depth_below m c args a Hin). apply IHa; [lia|apply Ha, Hin]. }
    split.
    - intros t Hd H. destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H1]]]]].
      + exact (Hroot m c args Hd H).
      + rewrite depth_nullable in Hd. exact (Hroot m c args ltac:(lia) H1).
    - intros [| | | |v o n| |] Hd H; simpl in H; try discriminate H. simpl in Hd |- *. apply IHt; [lia|exact H].
Qed.

Lemma in_fragment_ground: forall t, in_fragment env t = true -> ground t = true.
Proof.
    intros t H. unfold ground. rewrite (in_fragment_is_gfrag env t H).
    rewrite (proj1 (in_fragment_no_refs (depth t)) t (le_n _) H). reflexivity.
Qed.

(* A class type, nullable or not, an intersection of class types, nullable or not *)
Lemma ground_cases: forall t, ground t = true ->
    (exists m c args, t = RootResolved m c args)
    \/ (exists m c args, t = Nullable (RootResolved m c args))
    \/ (exists ys, t = Intersection ys /\ ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true)
    \/ (exists ys, t = Nullable (Intersection ys) /\ ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true).
Proof.
    assert (Hinter: forall ys, ground (Intersection ys) = true ->
        ys <> [] /\ forall y, In y ys -> is_class y = true /\ ground y = true).
    { intros ys H. unfold ground in H. apply andb_true_iff in H. destruct H as [Hg Hn].
      (* without references, the components don't keep their nullability *)
      destruct (is_nullable env (Intersection ys)) eqn:En.
      { exfalso. destruct (kept_has_reference env ys Hg En) as [g Hin]. simpl in Hn. rewrite forallb_forall in Hn.
        pose proof (Hn _ Hin) as Hng. simpl in Hng. discriminate Hng. }
      destruct (intersection_gfrag env ys Hg En) as [Hne Hc]. split; [exact Hne|].
      intros y Hy. destruct (Hc y Hy) as [Hcomp Hgy]. simpl in Hn. rewrite forallb_forall in Hn. pose proof (Hn y Hy) as Hny.
      destruct y as [| |g| | | |]; simpl in Hcomp; try discriminate Hcomp; try discriminate Hny.
      split; [reflexivity|unfold ground; apply andb_true_iff; split; [exact Hgy|exact Hny]]. }
    intros t H. pose proof H as H'. unfold ground in H'. apply andb_true_iff in H'. destruct H' as [Hg Hn].
    destruct t as [m c args|[m c args|n|g|me msg|v o n|g|ys]|g|me msg|v o n|g|ys]; simpl in Hg, Hn; try discriminate Hg;
        try discriminate Hn.
    - left. eauto.
    - right. left. eauto.
    - right. right. right. exists ys. split; [reflexivity|]. apply Hinter.
      unfold ground in H |- *. apply andb_true_iff in H. destruct H as [H1 H2].
      change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true) in H1.
      apply andb_true_iff in H1. apply andb_true_iff. split; [exact (proj2 H1)|exact H2].
    - right. right. left. exists ys. split; [reflexivity|]. exact (Hinter ys H).
Qed.

Lemma ground_nullable_inner: forall x, ground (Nullable x) = true -> ground x = true.
Proof.
    intros x H. unfold ground in *. apply andb_true_iff in H. destruct H as [Hg Hn]. simpl in Hg, Hn.
    apply andb_true_iff in Hg. rewrite (proj2 Hg), Hn. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* unify on ground types                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* A ground intersection, nullable or not, has components that aren't *)
Lemma ground_intersection_not_nullable: forall ys,
    ground (Intersection ys) = true \/ ground (Nullable (Intersection ys)) = true -> is_nullable env (Intersection ys) = false.
Proof.
    intros ys [H|H].
    { destruct (is_nullable env (Intersection ys)) eqn:En; [|reflexivity]. exfalso.
      pose proof (ground_gfrag _ H) as Hg. destruct (kept_has_reference env ys Hg En) as [g Hin].
      unfold ground in H. apply andb_true_iff in H. destruct H as [_ Hn]. simpl in Hn. rewrite forallb_forall in Hn.
      pose proof (Hn _ Hin) as Hng. simpl in Hng. discriminate Hng. }
    pose proof (ground_gfrag _ H) as Hg. change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true) in Hg.
    apply andb_true_iff in Hg. destruct Hg as [Hn _]. apply negb_true_iff, Hn.
Qed.

Ltac ground_intersection HX :=
    try (match goal with |- context [without_null env (Nullable (Intersection ?ys))] =>
        change (without_null env (Nullable (Intersection ys))) with (without_null env (Intersection ys)) end);
    match goal with |- context [without_null env (Intersection ?ys)] =>
        rewrite (without_null_not_nullable_intersection env ys
            (ground_intersection_not_nullable ys ltac:(first [left; exact HX|right; exact HX])))
    end.

(* A nullable target takes what the type in it takes without null *)
Lemma ground_nullable_target: forall n t y s, ground y = true ->
    unify env (S n) (Nullable t) y (Ongoing s) = unify env n t (without_null env y) (Ongoing s).
Proof.
    intros n t y s Hy.
    destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity.
    ground_intersection Hy. reflexivity.
Qed.

Lemma ground_rewrap: forall x, ground x = true -> rewrap_nullable x = Nullable (without_null env x).
Proof.
    intros x HX. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity;
        repeat ground_intersection HX; reflexivity.
Qed.

Lemma ground_without_null_idempotent: forall x, ground x = true -> without_null env (without_null env x) = without_null env x.
Proof.
    intros x HX. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity;
        repeat ground_intersection HX; reflexivity.
Qed.

Lemma ground_without_null: forall x, ground x = true -> ground (without_null env x) = true.
Proof.
    intros x HX. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
        try ground_intersection HX; first [exact HX|exact (ground_nullable_inner _ HX)].
Qed.

Lemma ground_non_null_without_null: forall x, ground x = true -> is_nullable env x = false -> without_null env x = x.
Proof.
    intros x HX Hn. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
        first [reflexivity|discriminate Hn|exact (without_null_not_nullable_intersection env ys Hn)].
Qed.

Lemma ground_without_null_not_nullable: forall x, ground x = true -> is_nullable env (without_null env x) = false.
Proof.
    intros x HX. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity.
    - rewrite (without_null_not_nullable_intersection env ys (ground_intersection_not_nullable ys (or_introl HX))).
      exact (ground_intersection_not_nullable ys (or_introl HX)).
    - change (without_null env (Nullable (Intersection ys))) with (without_null env (Intersection ys)).
      rewrite (without_null_not_nullable_intersection env ys (ground_intersection_not_nullable ys (or_intror HX))).
      exact (ground_intersection_not_nullable ys (or_intror HX)).
Qed.

Lemma no_refs_without_null: forall t, no_refs t = true -> no_refs (without_null env t) = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [without_null no_refs] in H |- *; try exact H;
        try exact (IH n H).
    destruct (forallb (is_nullable env) cs); [|exact H]. cbn [no_refs].
    induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
    rewrite (IH c (proj1 H)). exact (IHc (proj2 H)).
Qed.

Lemma no_refs_with_mutability: forall m0 t, no_refs t = true -> no_refs (with_mutability env m0 t) = true.
Proof.
    fix IH 2. intros m0 [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] H; cbn [with_mutability no_refs] in H |- *; try exact H.
    - pose proof (IH m0 n H) as Hn. destruct (with_mutability env m0 n); exact Hn.
    - exact (IH m0 n H).
    - match goal with |- context [map (with_mutability env ?x) _] => generalize x end. intros k'.
      induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH k' c (proj1 H)). exact (IHc (proj2 H)).
Qed.

(* An intersection of ground types, as ofComponents makes it, of the fragment, is ground *)
Lemma ground_of_components: forall ys, (forall y, In y ys -> ground y = true) ->
    gfrag env (of_components env (flat_map intersected_components ys)) = true ->
    ground (of_components env (flat_map intersected_components ys)) = true.
Proof.
    intros ys Hys Hg. unfold ground. rewrite Hg. cbn [andb].
    assert (Hz: forall z, In z (flat_map intersected_components ys) -> no_refs z = true).
    { intros z Hz. apply in_flat_map in Hz. destruct Hz as [y [Hy Hzy]]. pose proof (Hys y Hy) as Hgy.
      unfold ground in Hgy. apply andb_true_iff in Hgy. destruct Hgy as [_ Hny].
      destruct y as [| [| | | | | |cs] | | | | |cs]; cbn [intersected_components] in Hzy; try (destruct Hzy as [<-|[]]; exact Hny).
      - apply in_map_iff in Hzy. destruct Hzy as [d [<- Hd]]. cbn [no_refs] in Hny |- *. rewrite forallb_forall in Hny. exact (Hny d Hd).
      - cbn [no_refs] in Hny. rewrite forallb_forall in Hny. exact (Hny z Hzy). }
    clear Hg Hys. revert Hz. generalize (flat_map intersected_components ys) as zs. intros zs Hz.
    unfold of_components. destruct zs as [|z1 [|z2 zs']]; [reflexivity|exact (Hz z1 (or_introl eq_refl))|].
    cbv zeta. destruct (negb (forallb (is_nullable env) (z1 :: z2 :: zs'))); [|destruct (forallb is_nullable_type (z1 :: z2 :: zs'))];
        cbn [no_refs]; apply forallb_forall; intros w Hw; apply in_map_iff in Hw; destruct Hw as [c [<- Hc]];
        apply no_refs_with_mutability; first [apply no_refs_without_null, Hz, Hc | apply Hz, Hc].
Qed.

Lemma ground_rewrap_ground: forall x, ground x = true -> ground (rewrap_nullable x) = true.
Proof.
    intros x HX. destruct (ground_cases x HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try exact HX.
    cbn [rewrap_nullable]. unfold ground in HX |- *. apply andb_true_iff in HX. destruct HX as [Hg Hr].
    apply andb_true_iff. split; [|exact Hr].
    change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true). rewrite Hg, andb_true_r.
    change (negb (is_nullable env (Intersection ys)) = true). apply negb_true_iff.
    exact (ground_intersection_not_nullable ys (or_introl (proj2 (andb_true_iff _ _) (conj Hg Hr)))).
Qed.

Lemma ground_nullable_class: forall m c args, ground (RootResolved m c args) = true -> ground (Nullable (RootResolved m c args)) = true.
Proof. intros m c args H. exact H. Qed.

(* The components of ground types: class types, nullable or not *)
Definition flat_ground (z: EType): Prop :=
    ground z = true /\ (is_class z = true \/ exists m c args, z = Nullable (RootResolved m c args)).

Lemma flat_ground_components: forall ys z, (forall y, In y ys -> ground y = true) ->
    In z (flat_map intersected_components ys) -> flat_ground z.
Proof.
    intros ys z Hys Hz. apply in_flat_map in Hz. destruct Hz as [y [Hy Hzy]]. pose proof (Hys y Hy) as Hg.
    destruct (ground_cases y Hg) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ws [-> [_ Hws]]]|[ws [-> [_ Hws]]]]]];
        cbn [intersected_components] in Hzy.
    - destruct Hzy as [<-|[]]. split; [exact Hg|left; reflexivity].
    - destruct Hzy as [<-|[]]. split; [exact Hg|right; eauto].
    - destruct (Hws z Hzy) as [Hc Hgz]. split; [exact Hgz|left; exact Hc].
    - apply in_map_iff in Hzy. destruct Hzy as [w [<- Hw]]. destruct (Hws w Hw) as [Hc Hgw].
      destruct w as [m c args| | | | | |]; try discriminate Hc. split; [exact (ground_nullable_class m c args Hgw)|right; eauto].
Qed.

Lemma flat_length: forall ys, (forall y, In y ys -> ground y = true) -> length ys <= length (flat_map intersected_components ys).
Proof.
    induction ys as [|y ys IH]; intros H; [simpl; lia|]. cbn [flat_map]. rewrite length_app.
    pose proof (IH (fun y' Hy' => H y' (or_intror Hy'))).
    assert (1 <= length (intersected_components y)).
    { destruct (ground_cases y (H y (or_introl eq_refl))) as [[? [? [? ->]]]|[[? [? [? ->]]]|[[ws [-> [Hne _]]]|[ws [-> [Hne _]]]]]];
          cbn [intersected_components]; [simpl; lia|simpl; lia|destruct ws; [contradiction|simpl; lia]|destruct ws; [contradiction|simpl; lia]]. }
    simpl. lia.
Qed.

(* A class type, nullable or not, is the one component of itself *)
Lemma flat_map_singletons: forall ys, (forall y, In y ys -> flat_ground y) -> flat_map intersected_components ys = ys.
Proof.
    induction ys as [|y ys IH]; intros H; [reflexivity|]. cbn [flat_map].
    rewrite (IH (fun y' Hy' => H y' (or_intror Hy'))).
    destruct (H y (or_introl eq_refl)) as [_ [Hc|[m [c [args ->]]]]]; [destruct y; try discriminate Hc|]; reflexivity.
Qed.

(* The intersection of the components of ground types, without null, of their common mutability *)
Definition flat_intersection (zs: list EType): EType :=
    Intersection (map (fun c => with_mutability env (fold_left intersect_mutability (map (assignment_mutability env) zs) readonly)
        (without_null env c)) zs).

(* ofComponents of them: that, nullable where each of them is *)
Lemma ground_of_components_shape: forall zs, 2 <= length zs -> (forall z, In z zs -> flat_ground z) ->
    (forallb (is_nullable env) zs = false -> of_components env zs = flat_intersection zs)
    /\ (forallb (is_nullable env) zs = true -> of_components env zs = Nullable (flat_intersection zs)).
Proof.
    intros zs Hl Hz. unfold of_components, flat_intersection. destruct zs as [|z1 [|z2 zs']]; [simpl in Hl; lia|simpl in Hl; lia|].
    cbv beta iota zeta. split; intros E; rewrite E; cbn [negb]; [reflexivity|].
    replace (forallb is_nullable_type (z1 :: z2 :: zs')) with true; [reflexivity|]. symmetry. apply forallb_forall. intros z Hin.
    rewrite forallb_forall in E. pose proof (E z Hin) as Ez. destruct (Hz z Hin) as [_ [Hc|[m [c [args ->]]]]]; [|reflexivity].
    destruct z; try discriminate Hc. discriminate Ez.
Qed.

(* A ground type is told by its nullability and itself without null *)
Lemma ground_eq: forall x y, ground x = true -> ground y = true -> is_nullable env x = is_nullable env y ->
    without_null env x = without_null env y -> x = y.
Proof.
    intros x y HX HY En Ew. destruct (is_nullable env x) eqn:EX.
    - assert (HR: forall Z, ground Z = true -> is_nullable env Z = true -> Z = Nullable (without_null env Z)).
      { intros Z HZ EZ. rewrite <- (ground_rewrap Z HZ).
        destruct (ground_cases Z HZ) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
            try reflexivity; [discriminate EZ|rewrite (ground_intersection_not_nullable ys (or_introl HZ)) in EZ; discriminate EZ]. }
      rewrite (HR x HX EX), (HR y HY (eq_sym En)), Ew. reflexivity.
    - rewrite <- (ground_non_null_without_null x HX EX), <- (ground_non_null_without_null y HY (eq_sym En)). exact Ew.
Qed.

Lemma ground_keeps: forall n t y s s', ground t = true -> ground y = true ->
    unify env n t y (Ongoing s) = Some (Ongoing s') -> s' = s.
Proof.
    intros n t y s s' HD Hy H. pose proof (unify_free env wf n t y s s _ (ground_no_vars t HD) (ground_no_vars y Hy) H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

(* A non-null target takes no nullable value *)
Lemma ground_non_null: forall n t y s s', ground t = true -> ground y = true -> is_nullable env t = false ->
    unify env n t y (Ongoing s) = Some (Ongoing s') -> is_nullable env y = false.
Proof.
    intros [|n] t y s s' HD Hy Hn H; [discriminate H|].
    destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try reflexivity;
        try exact (ground_intersection_not_nullable ys (or_introl Hy));
    destruct (ground_cases t HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> _]]|[ds [-> _]]]]];
        try discriminate Hn;
        first [simpl in H; discriminate H | rewrite (unify_not_nullable_intersection env n ds _ s Hn) in H; discriminate H].
Qed.

(* Without null on both sides, what is taken stays taken *)
Lemma ground_unify_without_null: forall n t y s s', ground t = true -> ground y = true ->
    unify env n t y (Ongoing s) = Some (Ongoing s') -> unify env n (without_null env t) (without_null env y) (Ongoing s) = Some (Ongoing s').
Proof.
    intros n t y s s' HD Hy H.
    destruct (is_nullable env t) eqn:En.
    - destruct n as [|n]; [discriminate H|].
      destruct (ground_cases t HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> _]]|[ds [-> _]]]]].
      + discriminate En.
      + rewrite ground_nullable_target in H by exact Hy. apply (unify_fuel_monotone env n); [lia|exact H].
      + rewrite (ground_intersection_not_nullable ds (or_introl HD)) in En. discriminate En.
      + ground_intersection HD.
        rewrite ground_nullable_target in H by exact Hy. apply (unify_fuel_monotone env n); [lia|exact H].
    - rewrite (ground_non_null_without_null t HD En), (ground_non_null_without_null y Hy (ground_non_null n t y s s' HD Hy En H)).
      exact H.
Qed.

(* What a target takes is of no more mutability than it *)
Lemma ground_mutability: forall n t y s s', ground t = true -> ground y = true ->
    unify env n t y (Ongoing s) = Some (Ongoing s') -> Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env t) = true.
Proof.
    induction n as [|n IH]; intros t y s s' HD Hy H; [discriminate H|].
    destruct (ground_cases t HD) as [[md [cd [dargs ->]]]|[[md [cd [dargs ->]]]|[[ds [-> [Hne Hds]]]|[ds [-> [Hne Hds]]]]]].
    - destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> [_ Hys]]]|[ys [-> _]]]]].
      + rewrite unify_classes in H. destruct (base_type_is_subtype_of env c cd); [|discriminate H].
        destruct (Model.is_subtype_of _ _) eqn:Em; [reflexivity|discriminate H].
      + discriminate H.
      + destruct (intersection_flipped_unify_found env n _ ys s s' H) as [c [Hc Hu]].
        eapply mutability_subtype_trans; [apply intersection_assignment_mutability_below_component, Hc|].
        exact (IH _ c s s' HD (proj2 (Hys c Hc)) Hu).
      + discriminate H.
    - rewrite ground_nullable_target in H by exact Hy. change (assignment_mutability env (Nullable (RootResolved md cd dargs)))
          with (assignment_mutability env (RootResolved md cd dargs)).
      rewrite <- (without_null_keeps_assignment_mutability env ranked y).
      exact (IH _ _ s s' (ground_nullable_inner _ HD) (ground_without_null y Hy) H).
    - destruct (is_nullable env y) eqn:Eny.
      { destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
            try discriminate Eny; try (rewrite (ground_intersection_not_nullable ys (or_introl Hy)) in Eny; discriminate Eny);
            rewrite (unify_not_nullable_intersection env n ds _ s (ground_intersection_not_nullable ds (or_introl HD))) in H;
            discriminate H. }
      assert (Hshape: match y with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end)
          by (destruct (ground_cases y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]];
              first [exact I|discriminate Eny]).
      assert (Hnv: forall c, In c ds -> is_type_variable c = false)
          by (intros c Hc; pose proof (proj1 (Hds c Hc)) as Hcl; destruct c; first [reflexivity|discriminate Hcl]).
      destruct (intersection_target env n ds y s s' Hnv Hne Hshape (fun c u Hc E => ground_keeps n c y s u (proj2 (Hds c Hc)) Hy E) H) as [_ Hall].
      rewrite (intersection_assignment_mutability env). apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
      intros mc Hmc. apply in_map_iff in Hmc. destruct Hmc as [c [<- Hc]].
      exact (IH c y s s (proj2 (Hds c Hc)) Hy (Hall c Hc)).
    - rewrite ground_nullable_target in H by exact Hy. change (assignment_mutability env (Nullable (Intersection ds)))
          with (assignment_mutability env (Intersection ds)).
      rewrite <- (without_null_keeps_assignment_mutability env ranked y).
      exact (IH _ _ s s' (ground_nullable_inner _ HD) (ground_without_null y Hy) H).
Qed.

End Ground.

Section Wide.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable b: Bindings.
Variable d0: nat.
Hypothesis Hbf: bindings_in_fragment env b.

(* A component of an intersection that keeps the nullability of its components: `A?`, of a class type
   or a reference as components are otherwise, or a reference to a type parameter of a nullable bound,
   as it is *)
Definition is_kept_shape (c: EType): bool :=
    match c with Nullable n => is_component_shape env n | Generic _ => is_nullable env c | _ => false end.

(* The types instantiated: those of sfrag, the type arguments of which may be intersections, too, also
   ones that keep the nullability of their components *)
Fixpoint wfrag (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        Nat.eqb (length arguments) (length (parameter_ids env c))
        && forallb (fun a => match a with
            | TypeArgument _ _ n =>
                match n with
                | Intersection cs | Nullable (Intersection cs) =>
                    Nat.leb 2 (length cs) && forallb (fun c => is_component_shape env c && wfrag c) cs
                    || Nat.leb 2 (length cs) && forallb (fun c => is_kept_shape c && wfrag c) cs
                        && negb (forallb is_nullable_type cs)
                | _ => wfrag n
                end
            | _ => false
            end) arguments
    | Nullable n => (is_class n || is_generic n) && wfrag n
    | Generic _ => sfrag env t
    | _ => false
    end.

Definition wcomponents (cs: list EType): bool := Nat.leb 2 (length cs) && forallb (fun c => is_component_shape env c && wfrag c) cs.

Definition wtfrag (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) => wcomponents cs
    | _ => wfrag t
    end.

(* An intersection that keeps the nullability of its components, as ofComponents makes it where they
   may each be null but not all are written `X?`: `A? & P` with `P : Any?` *)
Definition kcomponents (cs: list EType): bool :=
    Nat.leb 2 (length cs) && forallb (fun c => is_kept_shape c && wfrag c) cs && negb (forallb is_nullable_type cs).

(* The types of generic code: those of the wide fragment, and such intersections, nullable or not, as
   type arguments are, too. Made nullable, `T?` with T bound to `A? & P`, as rewrap_nullable makes it:
   `(A? & P)?`, with the values of `(A & P!)?`, which NullableTypeReference makes *)
Definition ktfrag (t: EType): bool :=
    match t with
    | Intersection cs | Nullable (Intersection cs) => wcomponents cs || kcomponents cs
    | _ => wfrag t
    end.

Definition argument_wfrag (a: EType): bool := match a with TypeArgument _ _ n => ktfrag n | _ => false end.


(* An intersection of the fragment isn't nullable, its components aren't *)
Lemma wcomponents_not_nullable: forall cs, wcomponents cs = true -> is_nullable env (Intersection cs) = false.
Proof.
    intros cs Hcs. unfold wcomponents in Hcs. apply andb_true_iff in Hcs. destruct Hcs as [Hl Hcs'].
    destruct cs as [|c0 cs0]; [discriminate Hl|]. simpl in Hcs'. apply andb_true_iff in Hcs'. destruct Hcs' as [Hc0 _].
    apply andb_true_iff in Hc0. destruct Hc0 as [Hc0 _]. unfold is_component_shape in Hc0. apply andb_true_iff in Hc0.
    exact (intersection_not_nullable env (c0 :: cs0) c0 (or_introl eq_refl) (proj1 (negb_true_iff _) (proj2 Hc0))).
Qed.

Lemma wfrag_cases: forall t, wfrag t = true ->
    (exists m c args, t = RootResolved m c args /\ class_eqb c nothing = false
        /\ length args = length (parameter_ids env c) /\ forall a, In a args -> argument_wfrag a = true)
    \/ (exists m, t = RootResolved m nothing [])
    \/ (exists m c args, t = Nullable (RootResolved m c args) /\ wfrag (RootResolved m c args) = true)
    \/ (exists g, t = Generic g /\ generic_sfrag env g)
    \/ (exists g, t = Nullable (Generic g) /\ generic_sfrag env g).
Proof.
    assert (Hg: forall g, wfrag (Generic g) = true -> generic_sfrag env g).
    { intros g H. change (sfrag env (Generic g) = true) in H. apply (sfrag_generic_iff env wf) in H. exact H. }
    intros [m c args|[m c args| |g| | | |]| g | | | |] H; try discriminate H.
    - cbn [wfrag] in H. destruct (class_eqb c nothing) eqn:Hc.
      + right. left. apply class_eqb_true in Hc. subst c.
        exists m. apply andb_true_iff in H. destruct H as [Hl _]. apply Nat.eqb_eq in Hl.
        rewrite (nothing_arguments env wf args Hl). reflexivity.
      + left. apply andb_true_iff in H. destruct H as [Hl Ha]. exists m, c, args.
        split; [reflexivity|]. split; [exact Hc|]. split; [apply Nat.eqb_eq, Hl|].
        intros a Hin. rewrite forallb_forall in Ha. pose proof (Ha a Hin) as Ha'.
        destruct a as [| | | |v o n| |]; try discriminate Ha'. exact Ha'.
    - right. right. left. exists m, c, args. split; [reflexivity|]. simpl in H. exact H.
    - right. right. right. right. exists g. split; [reflexivity|]. apply Hg. simpl in H. exact H.
    - right. right. right. left. exists g. split; [reflexivity|]. exact (Hg g H).
Qed.

Lemma wtfrag_cases: forall t, wtfrag t = true ->
    wfrag t = true
    \/ (exists cs, t = Intersection cs /\ wcomponents cs = true)
    \/ (exists cs, t = Nullable (Intersection cs) /\ wcomponents cs = true).
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs];
        try (left; exact H).
    - right. right. exists cs. split; [reflexivity|exact H].
    - right. left. exists cs. split; [reflexivity|exact H].
Qed.

Lemma wcomponents_facts: forall cs, wcomponents cs = true ->
    2 <= length cs /\ forall C, In C cs -> is_component_shape env C = true /\ wfrag C = true.
Proof.
    intros cs H. unfold wcomponents in H. apply andb_true_iff in H. destruct H as [Hl H].
    split; [apply Nat.leb_le, Hl|]. intros C Hc. rewrite forallb_forall in H. apply andb_true_iff, H, Hc.
Qed.

Lemma wfrag_wtfrag: forall t, wfrag t = true -> wtfrag t = true.
Proof. intros [| [] | | | | |] H; try exact H; discriminate H. Qed.

Lemma sfrag_wfrag: forall t, sfrag env t = true -> wfrag t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (sfrag_cases env wf t H) as [[m [c [args [-> [Hc [Hl Hargs]]]]]]|[[m_bot ->]|[[m [c [args [-> Ht']]]]|[[g [-> _]]|[g [-> _]]]]]].
    - simpl. rewrite Hl, Nat.eqb_refl. apply forallb_forall. intros a Hin. pose proof (Hargs a Hin) as Ha.
      destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha.
      pose proof (esize_in args _ Hin) as Hs. simpl in Hs.
      assert (Hn: wfrag n = true) by (apply (IH (esize n)); [simpl; lia|reflexivity|exact Ha]).
      destruct (sfrag_cases env wf n Ha) as [[? [? [? [-> _]]]]|[[m_bot ->]|[[? [? [? [-> _]]]]|[[? [-> _]]|[? [-> _]]]]]]; exact Hn.
    - simpl. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity.
    - change ((is_class (RootResolved m c args) || is_generic (RootResolved m c args)) && wfrag (RootResolved m c args) = true).
      simpl (is_class _ || is_generic _). apply (IH (esize (RootResolved m c args))); [simpl; lia|reflexivity|exact Ht'].
    - exact H.
    - exact H.
Qed.

Lemma tfrag_wtfrag: forall t, tfrag env t = true -> wtfrag t = true.
Proof.
    intros t H. destruct (tfrag_cases env t H) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - exact (wfrag_wtfrag t (sfrag_wfrag t Hs)).
    - destruct (components_sfrag_facts env cs Hcs) as [Hl Hc]. unfold wtfrag, wcomponents.
      rewrite (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      rewrite Hsh, (sfrag_wfrag c Hs). reflexivity.
    - destruct (components_sfrag_facts env cs Hcs) as [Hl Hc]. unfold wtfrag, wcomponents.
      rewrite (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      rewrite Hsh, (sfrag_wfrag c Hs). reflexivity.
Qed.


Lemma ktfrag_cases: forall t, ktfrag t = true -> wtfrag t = true
    \/ (exists cs, t = Intersection cs /\ kcomponents cs = true) \/ (exists cs, t = Nullable (Intersection cs) /\ kcomponents cs = true).
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs]; try (left; exact H).
    - change (wcomponents cs || kcomponents cs = true) in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|].
      right. right. exists cs. split; [reflexivity|exact H].
    - change (wcomponents cs || kcomponents cs = true) in H. apply orb_true_iff in H. destruct H as [H|H]; [left; exact H|].
      right. left. exists cs. split; [reflexivity|exact H].
Qed.

Lemma wtfrag_ktfrag: forall t, wtfrag t = true -> ktfrag t = true.
Proof.
    intros t H. destruct t as [m c args|[m c args|n|g|me msg|v o n|g|cs]|g|me msg|v o n|g|cs]; try exact H;
        change (wcomponents cs || kcomponents cs = true); change (wcomponents cs = true) in H; rewrite H; reflexivity.
Qed.

Lemma ktfrag_nullable_inner: forall t0, ktfrag (Nullable t0) = true -> ktfrag t0 = true.
Proof. intros t0 H. destruct t0; try discriminate H; exact H. Qed.

Lemma kept_ktfrag: forall cs, kcomponents cs = true -> ktfrag (Intersection cs) = true /\ ktfrag (Nullable (Intersection cs)) = true.
Proof. intros cs H. split; change (wcomponents cs || kcomponents cs = true); rewrite H, orb_true_r; reflexivity. Qed.

Lemma kcomponents_facts: forall cs, kcomponents cs = true ->
    2 <= length cs /\ (forall C, In C cs -> is_kept_shape C = true /\ wfrag C = true)
    /\ exists g, In (Generic g) cs /\ is_nullable env (Generic g) = true.
Proof.
    intros cs H. unfold kcomponents in H. apply andb_true_iff in H. destruct H as [H Hn]. apply andb_true_iff in H.
    destruct H as [Hl H]. rewrite forallb_forall in H. apply negb_true_iff in Hn.
    split; [apply Nat.leb_le, Hl|]. split; [intros C Hc; apply andb_true_iff, H, Hc|].
    assert (Hex: exists C, In C cs /\ is_nullable_type C = false).
    { clear -Hn. induction cs as [|C cs IH]; [discriminate Hn|]. cbn [forallb] in Hn.
      destruct (is_nullable_type C) eqn:E.
      - destruct (IH Hn) as [c' [Hc' E']]. exists c'. split; [right; exact Hc'|exact E'].
      - exists C. split; [left; reflexivity|exact E]. }
    destruct Hex as [C [Hc E]]. pose proof (H C Hc) as Hk. apply andb_true_iff in Hk. destruct Hk as [Hk _].
    destruct C as [|n|g| | | |]; try discriminate Hk; [discriminate E|]. exists g. split; [exact Hc|exact Hk].
Qed.

Lemma kcomponents_nullable: forall cs, kcomponents cs = true -> is_nullable env (Intersection cs) = true.
Proof.
    intros cs H. destruct (kcomponents_facts cs H) as [_ [Hc _]]. cbn [is_nullable]. apply forallb_forall.
    intros c Hin. destruct (Hc c Hin) as [Hk _]. destruct c; try discriminate Hk; [reflexivity|exact Hk].
Qed.

(* A component of such an intersection, without null: one of an intersection of the wide fragment *)
Lemma kept_shape_without_null: forall x, is_kept_shape x = true -> wfrag x = true ->
    is_component_shape env (without_null env x) = true /\ wfrag (without_null env x) = true.
Proof.
    intros [m d args|n|g|me msg|v o n|g|cs] Hk Hw; cbn [is_kept_shape] in Hk; try discriminate Hk.
    - assert (Hn: is_nullable env n = false)
          by (unfold is_component_shape in Hk; apply andb_true_iff in Hk; apply negb_true_iff, (proj2 Hk)).
      change (without_null env (Nullable n)) with (without_null env n). rewrite (without_null_unchanged env n Hn).
      split; [exact Hk|]. cbn [wfrag] in Hw. apply andb_true_iff in Hw. exact (proj2 Hw).
    - change (sfrag env (Generic g) = true) in Hw.
      destruct (tfrag_without_null env wf _ (Generic g) (le_n _) (sfrag_tfrag env _ Hw)) as [Ht [_ Hn]].
      rewrite (without_null_generic env g) in Ht, Hn |- *. split; [unfold is_component_shape; rewrite Hn; reflexivity|exact Ht].
Qed.

Lemma kept_without_null_shape: forall cs, kcomponents cs = true ->
    without_null env (Intersection cs) = Intersection (map (without_null env) cs) /\ wcomponents (map (without_null env) cs) = true.
Proof.
    intros cs H. destruct (kcomponents_facts cs H) as [Hl [Hc _]]. split.
    - pose proof (kcomponents_nullable cs H) as En. cbn [is_nullable] in En. cbn [without_null]. rewrite En. reflexivity.
    - unfold wcomponents. rewrite length_map, (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c' Hc'.
      apply in_map_iff in Hc'. destruct Hc' as [c [<- Hin]]. destruct (Hc c Hin) as [Hk Hw].
      destruct (kept_shape_without_null c Hk Hw) as [Hs Hf]. rewrite Hs, Hf. reflexivity.
Qed.

End Wide.

Section WideInstances.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable b: Bindings.
Variable d0: nat.
Hypothesis Hbf: bindings_in_fragment env b.

Lemma intersect_classes: forall ys, (forall y, In y ys -> is_class y = true) ->
    intersect_instances env ys = of_components env (flat_map intersected_components ys).
Proof.
    intros ys H. apply intersect_instances_plain. intros t Ht. pose proof (H t Ht) as Hc.
    destruct t; first [reflexivity|discriminate Hc].
Qed.

Lemma of_class_types: forall ys, 2 <= length ys -> (forall y, In y ys -> is_class y = true) ->
    of_components env (flat_map intersected_components ys) = Intersection (map (with_mutability env (common_mutability env ys)) ys).
Proof.
    intros ys Hl H. rewrite (flat_map_classes ys H). rewrite (of_components_many env ys Hl).
    - f_equal. apply map_ext_in. intros y Hy. pose proof (H y Hy) as Hc. destruct y; try discriminate Hc. reflexivity.
    - destruct ys as [|y1 ys']; [simpl in Hl; lia|]. pose proof (H y1 (or_introl eq_refl)) as Hc.
      destruct y1; try discriminate Hc. reflexivity.
Qed.

Lemma ground_with_mutability: forall m0 y, is_class y = true -> ground env y = true ->
    ground env (with_mutability env m0 y) = true /\ is_class (with_mutability env m0 y) = true.
Proof. intros m0 [m c args| | | | | |] Hc Hy; try discriminate Hc. split; [exact Hy|reflexivity]. Qed.

Lemma flat_without_null: forall z, flat_ground env z -> ground env (without_null env z) = true /\ is_class (without_null env z) = true.
Proof.
    intros z [Hg [Hc|[m [c [args ->]]]]].
    - destruct z; try discriminate Hc. split; [exact Hg|reflexivity].
    - split; [exact (ground_nullable_inner env _ Hg)|reflexivity].
Qed.

Lemma flat_intersection_eq: forall zs, flat_intersection env zs
    = Intersection (map (with_mutability env (common_mutability env (map (without_null env) zs))) (map (without_null env) zs)).
Proof.
    intros zs. unfold flat_intersection, common_mutability.
    assert (E: map (assignment_mutability env) (map (without_null env) zs) = map (assignment_mutability env) zs).
    { rewrite map_map. apply map_ext. intros w. apply (without_null_keeps_assignment_mutability env ranked). }
    rewrite E, map_map. reflexivity.
Qed.

(* Of the components of ground types, the intersection without null is ground and non-null, of class
   types *)
Lemma flat_intersection_ground: forall zs, zs <> [] -> (forall z, In z zs -> flat_ground env z) ->
    ground env (flat_intersection env zs) = true /\ is_nullable env (flat_intersection env zs) = false
    /\ forall y, In y (intersected_components (flat_intersection env zs)) -> ground env y = true /\ is_class y = true.
Proof.
    intros zs Hne Hz. rewrite flat_intersection_eq. cbn [intersected_components].
    set (ws := map (without_null env) zs).
    assert (Hws: forall w, In w ws -> ground env w = true /\ is_class w = true).
    { intros w Hw. unfold ws in Hw. apply in_map_iff in Hw. destruct Hw as [z [<- Hin]]. exact (flat_without_null z (Hz z Hin)). }
    assert (Hne': ws <> []) by (unfold ws; destruct zs; [contradiction|discriminate]).
    clearbody ws.
    assert (Hys: forall y, In y (map (with_mutability env (common_mutability env ws)) ws) -> ground env y = true /\ is_class y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [w [<- Hw]]. destruct (Hws w Hw) as [Hg Hc].
      exact (ground_with_mutability _ _ Hc Hg). }
    split; [|split; [|exact Hys]].
    - unfold ground. apply andb_true_iff. split.
      + apply (Fragment.make_intersection_gfrag env).
        * destruct ws; [contradiction|discriminate].
        * intros y Hy. destruct (Hys y Hy) as [Hg Hc]. destruct y; try discriminate Hc. split; [reflexivity|exact (ground_gfrag env _ Hg)].
        * intros y Hy. apply internal_Mutability_dec_bl.
          exact (proj1 (forallb_forall _ _) (common_classes_uniform env ws Hne' (fun w Hw => proj2 (Hws w Hw))) y Hy).
      + change (forallb no_refs (map (with_mutability env (common_mutability env ws)) ws) = true). apply forallb_forall.
        intros y Hy. destruct (Hys y Hy) as [Hg _]. unfold ground in Hg. apply andb_true_iff in Hg. apply Hg.
    - destruct ws as [|w ws']; [contradiction|].
      apply (intersection_not_nullable env (map (with_mutability env (common_mutability env (w :: ws'))) (w :: ws'))
          (with_mutability env (common_mutability env (w :: ws')) w) (or_introl eq_refl)).
      destruct (Hys _ (or_introl eq_refl)) as [_ Hc]. destruct (with_mutability env _ w); try discriminate Hc. reflexivity.
Qed.

(* Instantiated, a type of the wide fragment is ground, and mentions no type parameter bound loosely *)
Lemma wide_instance: forall t, ktfrag env t = true -> bound_in env b d0 [] t = true ->
    ground env (instantiate env b t) = true
    /\ mentions_loosely_bound b t = false /\ mentions_loosely_bound_in_arguments b t = false
    /\ nests_argument (instantiate env b t) = false
    /\ (is_nullable env t = false -> is_nullable env (instantiate env b t) = false)
    /\ (is_component_shape env t = true -> is_class (instantiate env b t) = true).
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht Hb.
    (* a class type *)
    assert (Hroot: forall m c args, esize (RootResolved m c args) <= esize t -> wfrag env (RootResolved m c args) = true ->
        bound_in env b d0 [] (RootResolved m c args) = true ->
        ground env (RootResolved m c (map (instantiate env b) args)) = true /\ existsb (mentions_loosely_bound b) args = false).
    { intros m c args Hd Hf Hb'.
      destruct (wfrag_cases env wf (RootResolved m c args) Hf)
          as [[m' [c' [args' [Heq [_ [Hl Hargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
          try discriminate Heq.
      - injection Heq as <- <- <-.
        assert (Hall: forall a, In a args -> argument_gfrag env (instantiate env b a) = true
            /\ no_refs (instantiate env b a) = true /\ mentions_loosely_bound b a = false).
        { intros a Hin. pose proof (Hargs a Hin) as Ha. pose proof (bound_in_root env b d0 [] m c args Hb' a Hin) as Hba.
          pose proof (esize_in args a Hin) as Hs.
          destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha, Hs.
          destruct (bound_in_argument env b d0 [] v o n Hba) as [_ Hbn].
          destruct (IH (esize n) ltac:(simpl in Hd; lia) n eq_refl Ha Hbn) as [Hg [Hm [Hmi [Hnest _]]]].
          rewrite (instantiate_argument_plain env b v o n _ eq_refl Hmi Hnest).
          unfold ground in Hg. apply andb_true_iff in Hg. destruct Hg as [Hg Hn].
          split; [exact Hg|split; [exact Hn|exact Hm]]. }
        split.
        + unfold ground. apply andb_true_iff. split.
          * change (Nat.eqb (length (map (instantiate env b) args)) (length (parameter_ids env c))
                && forallb (argument_gfrag env) (map (instantiate env b) args) = true).
            rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
            destruct Ha' as [a [<- Hin]]. apply (Hall a Hin).
          * change (forallb no_refs (map (instantiate env b) args) = true). apply forallb_forall. intros a' Ha'.
            apply in_map_iff in Ha'. destruct Ha' as [a [<- Hin]]. apply (Hall a Hin).
        + apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Hin E]].
          rewrite (proj2 (proj2 (Hall a Hin))) in E. discriminate E.
      - injection Heq as _ -> ->. split; [|reflexivity].
        unfold ground. simpl. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
    (* a reference to a type parameter *)
    assert (Hgen: forall g, generic_sfrag env g -> bound_in env b d0 [] (Generic g) = true ->
        in_fragment env (instantiate env b (Generic g)) = true /\ mentions_loosely_bound b (Generic g) = false
        /\ (is_nullable env (Generic g) = false -> is_nullable env (instantiate env b (Generic g)) = false)
        /\ nests_argument (instantiate env b (Generic g)) = false).
    { intros g Hg Hb'. destruct (binds_ref_some env wf b d0 [] g Hb') as [o [x [E [Ho [Hx _]]]]].
      destruct (instantiate_exact_generic env b g o x E Ho Hx) as [Hi Hm].
      pose proof (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg)) as Htf.
      pose proof (proj2 (proj2 (instance_facts env wf b d0 [] Hbf _ (Generic g) (le_n _) Htf Hb'))) as Hn.
      rewrite (inst_nested_instantiate env wf b d0 [] (Generic g) Htf Hb') in Hn.
      rewrite Hi in Hn |- *. split; [exact (inst_ref_in_fragment env g x (Hbf _ o x E))|].
      split; [exact Hm|split; [exact Hn|exact (gfrag_inst_ref_flat env g x Hx)]]. }
    destruct (ktfrag_cases env t Ht) as [Ht'|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    2: { (* an intersection whose components keep their nullability: of class types, nullable or not *)
      destruct (kcomponents_facts env cs Hcs) as [Hl [Hc _]].
      assert (Hall: forall c, In c cs -> flat_ground env (instantiate env b c)
          /\ mentions_loosely_bound b c = false /\ mentions_loosely_bound_in_arguments b c = false).
      { intros c Hin. destruct (Hc c Hin) as [Hkc Hwc]. pose proof (esize_in cs c Hin) as Hs.
        pose proof (bound_in_component env b d0 [] cs c Hb Hin) as Hbc.
        destruct (IH (esize c) ltac:(simpl; lia) c eq_refl (wtfrag_ktfrag env c (wfrag_wtfrag env c Hwc)) Hbc)
            as [Hg [Hm [Hmi _]]].
        split; [|exact (conj Hm Hmi)]. split; [exact Hg|].
        destruct c as [m d args|n|g|me msg|v o n|g|cs']; cbn [is_kept_shape] in Hkc; try discriminate Hkc.
        - assert (Hwn: wfrag env n = true) by (cbn [wfrag] in Hwc; apply andb_true_iff in Hwc; exact (proj2 Hwc)).
          change (bound_in env b d0 [] n = true) in Hbc.
          destruct (IH (esize n) ltac:(simpl in Hs |- *; lia) n eq_refl (wtfrag_ktfrag env n (wfrag_wtfrag env n Hwn)) Hbc)
              as [_ [_ [_ [_ [_ Hcn]]]]].
          pose proof (Hcn Hkc) as Hcl'. change (instantiate env b (Nullable n)) with (rewrap_nullable (instantiate env b n)).
          destruct (instantiate env b n) as [mi di ai| | | | | |]; try discriminate Hcl'. cbn [rewrap_nullable]. right. eauto.
        - destruct (binds_ref_some env wf b d0 [] g Hbc) as [o [x [Ex [Ho [Hx _]]]]].
          rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
          destruct (fragment_cases env _ (inst_ref_in_fragment env g x (Hbf _ o x Ex))) as [[m [d [args E]]]|[m [d [args [E _]]]]];
              rewrite E; [left; reflexivity|right; eauto]. }
      set (ys := map (instantiate env b) cs).
      assert (Hfg: forall y, In y ys -> flat_ground env y)
          by (intros y Hy; unfold ys in Hy; apply in_map_iff in Hy; destruct Hy as [c [<- Hin]]; exact (proj1 (Hall c Hin))).
      assert (Heq: instantiate env b (Intersection cs) = of_components env ys).
      { change (instantiate env b (Intersection cs)) with (intersect_instances env ys).
        rewrite intersect_instances_plain, (flat_map_singletons env ys Hfg); [reflexivity|].
        intros y Hy. destruct (Hfg y Hy) as [_ [Hcl|[m [d [args ->]]]]]; [destruct y; first [reflexivity|discriminate Hcl]|reflexivity]. }
      assert (Hl': 2 <= length ys) by (unfold ys; rewrite length_map; exact Hl).
      assert (Hne: ys <> []) by (destruct ys; [simpl in Hl'; lia|discriminate]).
      destruct (flat_intersection_ground ys Hne Hfg) as [HN _].
      assert (HG: ground env (of_components env ys) = true).
      { destruct (forallb (is_nullable env) ys) eqn:E.
        - rewrite (proj2 (ground_of_components_shape env ys Hl' Hfg) E). exact (ground_rewrap_ground env _ HN).
        - rewrite (proj1 (ground_of_components_shape env ys Hl' Hfg) E). exact HN. }
      rewrite Heq. split; [exact HG|]. split.
      { change (existsb (mentions_loosely_bound b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj1 (proj2 (Hall c Hin))) in E. discriminate E. }
      split.
      { change (existsb (mentions_loosely_bound_in_arguments b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj2 (proj2 (Hall c Hin))) in E. discriminate E. }
      split; [destruct (ground_cases env _ HG) as [[? [? [? E]]]|[[? [? [? E]]]|[[? [E _]]|[? [E _]]]]]; rewrite E; reflexivity|].
      split; [intros Hn; rewrite (kcomponents_nullable env cs Hcs) in Hn; discriminate Hn|intros H0; discriminate H0]. }
    2: { (* the same, made nullable *)
      destruct (IH (esize (Intersection cs)) ltac:(simpl; lia) (Intersection cs) eq_refl (proj1 (kept_ktfrag env cs Hcs)) Hb)
          as [Hg [Hm [Hmi _]]].
      change (instantiate env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate env b (Intersection cs))).
      pose proof (ground_rewrap_ground env _ Hg) as HG.
      split; [exact HG|]. split; [exact Hm|]. split; [exact Hmi|].
      split; [destruct (ground_cases env _ HG) as [[? [? [? E]]]|[[? [? [? E]]]|[[? [E _]]|[? [E _]]]]]; rewrite E; reflexivity|].
      split; intros H0; discriminate H0. }
    clear Ht. rename Ht' into Ht.
    destruct (wtfrag_cases env t Ht) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + rewrite instantiate_class. destruct (Hroot m c args (le_n _) Hw Hb) as [Hg Hm].
        split; [exact Hg|]. change (mentions_loosely_bound b (RootResolved m c args)) with (existsb (mentions_loosely_bound b) args).
        change (mentions_loosely_bound_in_arguments b (RootResolved m c args)) with (existsb (mentions_loosely_bound b) args).
        rewrite Hm. repeat split; reflexivity.
      + unfold bottom_type in *. rewrite instantiate_class. destruct (Hroot _ _ _ (le_n _) Hw Hb) as [Hg Hm].
        split; [exact Hg|]. repeat split; reflexivity.
      + rewrite instantiate_nullable_class. destruct (Hroot m c args ltac:(simpl; lia) Ht' Hb) as [Hg Hm].
        split; [exact Hg|]. change (mentions_loosely_bound b (Nullable (RootResolved m c args))) with (existsb (mentions_loosely_bound b) args).
        change (mentions_loosely_bound_in_arguments b (Nullable (RootResolved m c args))) with (existsb (mentions_loosely_bound b) args).
        rewrite Hm. repeat split; try reflexivity; intros H0; discriminate H0.
      + destruct (Hgen g Hg Hb) as [Hf [Hm [Hn Hnest]]]. split; [exact (in_fragment_ground env _ Hf)|].
        split; [exact Hm|]. split; [reflexivity|]. split; [exact Hnest|]. split; [exact Hn|].
        intros Hsh. pose proof (Hn (component_non_null env _ Hsh)) as Hn'.
        destruct (fragment_cases env _ Hf) as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E in Hn' |- *;
            [reflexivity|discriminate Hn'].
      + destruct (Hgen g Hg Hb) as [Hf [Hm _]].
        change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
        pose proof (in_fragment_rewrap env _ Hf) as Hf'.
        split; [exact (in_fragment_ground env _ Hf')|]. split; [exact Hm|]. split; [reflexivity|].
        split; [exact (fragment_not_nesting env _ Hf')|]. split; intros H0; discriminate H0.
    - (* an intersection *)
      destruct (wcomponents_facts env cs Hcs) as [Hl Hc].
      assert (Hall: forall c, In c cs -> ground env (instantiate env b c) = true /\ is_class (instantiate env b c) = true
          /\ mentions_loosely_bound b c = false /\ mentions_loosely_bound_in_arguments b c = false).
      { intros c Hin. destruct (Hc c Hin) as [Hsh Hwc]. pose proof (esize_in cs c Hin) as Hs.
        destruct (IH (esize c) ltac:(simpl; lia) c eq_refl (wtfrag_ktfrag env c (wfrag_wtfrag env c Hwc)) (bound_in_component env b d0 [] cs c Hb Hin))
            as [Hg [Hm [Hmi [_ [_ Hcl]]]]].
        exact (conj Hg (conj (Hcl Hsh) (conj Hm Hmi))). }
      assert (Hys: forall y, In y (map (instantiate env b) cs) -> is_class y = true).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. apply (Hall c Hin). }
      change (instantiate env b (Intersection cs)) with (intersect_instances env (map (instantiate env b) cs)).
      rewrite (intersect_classes _ Hys), (of_class_types _ ltac:(rewrite length_map; exact Hl) Hys).
      assert (Hnn: forall k xs, xs <> [] -> (forall x, In x xs -> is_class x = true) ->
          is_nullable env (Intersection (map (with_mutability env k) xs)) = false).
      { intros k [|x xs] Hne Hx; [contradiction|]. apply (intersection_not_nullable env (map (with_mutability env k) (x :: xs)) (with_mutability env k x) (or_introl eq_refl)).
        pose proof (Hx x (or_introl eq_refl)) as Hcx. destruct x; try discriminate Hcx. reflexivity. }
      split; [|split; [|split; [|split; [reflexivity|split;
          [intros _; apply Hnn; [destruct cs; [simpl in Hl; lia|discriminate]|exact Hys]|intros H0; discriminate H0]]]]].
      + unfold ground. apply andb_true_iff. split.
        * set (ys := map (instantiate env b) cs) in *.
          pose proof (common_classes_uniform env ys ltac:(unfold ys; destruct cs; [simpl in Hl; lia|discriminate]) Hys) as Hu.
          apply (Fragment.make_intersection_gfrag env).
          -- unfold ys. destruct cs as [|c1 cs']; simpl in Hl |- *; [lia|discriminate].
          -- intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. unfold ys in Hy'.
             apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]]. destruct (Hall c Hin) as [Hg [Hcl _]].
             destruct (ground_with_mutability (common_mutability env (map (instantiate env b) cs)) _ Hcl Hg) as [Hg' Hcl'].
             split; [|apply (ground_gfrag env), Hg']. fold ys.
             destruct (instantiate env b c) as [| | | | | |]; try discriminate Hcl. reflexivity.
          -- intros y Hy. apply internal_Mutability_dec_bl. exact (proj1 (forallb_forall _ _) Hu y Hy).
        * change (forallb no_refs (map (with_mutability env (common_mutability env (map (instantiate env b) cs)))
              (map (instantiate env b) cs)) = true).
          apply forallb_forall. intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']].
          apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]]. destruct (Hall c Hin) as [Hg [Hcl _]].
          destruct (ground_with_mutability (common_mutability env (map (instantiate env b) cs)) _ Hcl Hg) as [Hg' _].
          unfold ground in Hg'. apply andb_true_iff in Hg'. apply Hg'.
      + change (existsb (mentions_loosely_bound b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj1 (proj2 (proj2 (Hall c Hin)))) in E. discriminate E.
      + change (existsb (mentions_loosely_bound_in_arguments b) cs = false). apply not_true_iff_false. intros E.
        apply existsb_exists in E. destruct E as [c [Hin E]]. rewrite (proj2 (proj2 (proj2 (Hall c Hin)))) in E. discriminate E.
    - (* a nullable intersection *)
      destruct (IH (esize (Intersection cs)) ltac:(simpl; lia) (Intersection cs) eq_refl (wtfrag_ktfrag env (Intersection cs) Hcs) Hb)
          as [Hg [Hm [Hmi [_ [Hn _]]]]].
      change (instantiate env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate env b (Intersection cs))).
      assert (Hnc: is_nullable env (Intersection cs) = false).
      { unfold wtfrag, wcomponents in Hcs. apply andb_true_iff in Hcs. destruct Hcs as [Hl Hcs'].
        destruct cs as [|c0 cs0]; [discriminate Hl|]. simpl in Hcs'. apply andb_true_iff in Hcs'. destruct Hcs' as [Hc0 _].
        apply andb_true_iff in Hc0. destruct Hc0 as [Hc0 _]. unfold is_component_shape in Hc0. apply andb_true_iff in Hc0.
        exact (intersection_not_nullable env (c0 :: cs0) c0 (or_introl eq_refl) (proj1 (negb_true_iff _) (proj2 Hc0))). }
      pose proof (Hn Hnc) as Hn'.
      destruct (ground_cases env _ Hg) as [[m [c [args E]]]|[[m [c [args E]]]|[[ys [E _]]|[ys [E _]]]]];
          rewrite E in Hg, Hn' |- *; try discriminate Hn'; cbn [rewrap_nullable].
      + split; [exact Hg|]. split; [exact Hm|]. split; [exact Hmi|]. split; [reflexivity|]. split; intros H0; discriminate H0.
      + split.
        { unfold ground in Hg |- *. apply andb_true_iff in Hg. destruct Hg as [Hg1 Hg2]. apply andb_true_iff. split; [|exact Hg2].
          change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true). rewrite Hg1, andb_true_r.
          apply negb_true_iff, Hn'. }
        split; [exact Hm|]. split; [exact Hmi|]. split; [reflexivity|]. split; intros H0; discriminate H0.
Qed.

(* A type argument of the wide fragment, instantiated *)
Lemma wide_argument: forall a, argument_wfrag env a = true -> bound_in env b d0 [] a = true ->
    exists v o y, a = TypeArgument v o y /\ instantiate env b a = TypeArgument v (instantiate_ownership b o) (instantiate env b y)
        /\ ktfrag env y = true /\ bound_in env b d0 [] y = true /\ ownership_bound b o = true
        /\ argument_gfrag env (instantiate env b a) = true /\ no_refs (instantiate env b a) = true
        /\ is_loose (instantiate env b a) = is_loose a /\ mentions_loosely_bound b a = false.
Proof.
    intros [| | | |v o y| |] Ha Hb; try discriminate Ha. exists v, o, y. simpl in Ha.
    destruct (bound_in_argument env b d0 [] v o y Hb) as [Ho Hbn].
    destruct (wide_instance y Ha Hbn) as [Hg [Hm [Hmi [Hnest _]]]].
    pose proof (instantiate_argument_plain env b v o y _ eq_refl Hmi Hnest) as Hi.
    rewrite Hi. unfold ground in Hg. apply andb_true_iff in Hg. destruct Hg as [Hg Hn].
    repeat split; try assumption.
    simpl. destruct o as [| | |q]; try reflexivity. simpl in Ho |- *.
    destruct (lookup_binding b q) as [[| | | |v' o' x| |]|]; try discriminate Ho. destruct v'; try discriminate Ho.
    destruct o'; try discriminate Ho; reflexivity.
Qed.

End WideInstances.

Section WideTemplates.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable b: Bindings.
Variable d: nat.
Hypothesis Hbf: bindings_in_fragment env b.

Section Templates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> argument_wfrag env y = true /\ bound_in env b d [] y = true.

Let bS := bindings_of env sub ys.
Let bL := bindings_of env sub (map (instantiate env b) ys).

Lemma wide_ys_type_argument: forall y, In y ys -> is_type_argument y = true.
Proof.
    intros y Hy. destruct (Hys y Hy) as [Ha _]. destruct y as [| | | |v o n| |]; try discriminate Ha. reflexivity.
Qed.

Lemma wide_template_instances: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        wfrag env (instantiate env bS t) = true /\ bound_in env b d [] (instantiate env bS t) = true)
    /\ (forall x, argument_depth x <= k -> template_argument env sub x = true ->
        argument_wfrag env (instantiate env bS x) = true /\ bound_in env b d [] (instantiate env bS x) = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true
        /\ bound_in env b d [] (RootResolved m c (map (instantiate env bS) targs)) = true).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      assert (Hall: forall a, In a targs -> argument_wfrag env (instantiate env bS a) = true
          /\ bound_in env b d [] (instantiate env bS a) = true).
      { intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
      split.
      - cbn [wfrag]. rewrite length_map, Hl, Nat.eqb_refl. apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'.
        destruct Ha' as [a [<- Ha]]. pose proof (proj1 (Hall a Ha)) as Hw.
        destruct (instantiate env bS a) as [| | | |v o n| |]; try discriminate Hw. exact Hw.
      - change (forallb (bound_in env b d []) (map (instantiate env bS) targs) = true). apply forallb_forall.
        intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. apply Hall, Ha. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite instantiate_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class.
        destruct (Hroot m c targs ltac:(lia) Ht') as [Hf Hb]. split; [|exact Hb].
        change ((is_class (RootResolved m c (map (instantiate env bS) targs)) || is_generic (RootResolved m c (map (instantiate env bS) targs)))
            && wfrag env (RootResolved m c (map (instantiate env bS) targs)) = true). rewrite Hf. reflexivity.
    - intros x Hd Hr. destruct (template_kind env sub x Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy (wide_ys_type_argument y (nth_error_In _ _ Hy))).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd. destruct (IHt n ltac:(lia) Hn') as [Hf Hb].
        pose proof (wtfrag_ktfrag env _ (wfrag_wtfrag env _ Hf)) as Hf'.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        assert (Hob: ownership_bound b o = true) by (destruct o; first [reflexivity|discriminate Ho]).
        destruct (mentions_loosely_bound bS n); [destruct v|]; cbn [argument_wfrag bound_in];
            rewrite ?Hob, ?Hf', ?Hb; split; first [reflexivity|exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ (bottom_in_sfrag env wf)))].
Qed.

Lemma wide_template_looseness: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        mentions_loosely_bound bL t = mentions_loosely_bound bS t)
    /\ (forall x, argument_depth x <= k -> template_argument env sub x = true ->
        mentions_loosely_bound bL x = mentions_loosely_bound bS x).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound bL) targs = existsb (mentions_loosely_bound bS) targs).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs]. apply existsb_ext_in.
      intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite !mentions_nullable, !mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros x Hd Hr. destruct (template_kind env sub x Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate env b) ys) i = Some (instantiate env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        unfold bL, bS. rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub _ i p _ Hi Hy')).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub ys i p y Hi Hy)).
        destruct (Hys y (nth_error_In _ _ Hy)) as [Ha Hb].
        destruct (wide_argument env wf b d Hbf y Ha Hb) as [v [o [n [_ [_ [_ [_ [_ [_ [_ [Hl _]]]]]]]]]]]. exact Hl.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

Lemma wide_template_commutes: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        instantiate env b (instantiate env bS t) = instantiate env bL t)
    /\ (forall x, argument_depth x <= k -> template_argument env sub x = true ->
        instantiate env b (instantiate env bS x) = instantiate env bL x).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true ->
        map (instantiate env b) (map (instantiate env bS) targs) = map (instantiate env bL) targs).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      rewrite map_map. apply map_ext_in. intros a Ha. pose proof (argument_depth_below m c targs a Ha).
      apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite !instantiate_class, (Hroot m c targs Hd Ht). reflexivity.
      + rewrite depth_nullable in Hd. rewrite !instantiate_nullable_class, (Hroot m c targs ltac:(lia) Ht'). reflexivity.
    - intros x Hd Hr. destruct (template_kind env sub x Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate env b) ys) i = Some (instantiate env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        destruct (Hys y (nth_error_In _ _ Hy)) as [Ha Hb].
        destruct (wide_argument env wf b d Hbf y Ha Hb) as [vy [oy [ny [_ [Ei _]]]]].
        unfold bS, bL. rewrite (selects env wf sub ys p bp i y Hi Hy (wide_ys_type_argument y (nth_error_In _ _ Hy))).
        rewrite (selects env wf sub _ p bp i _ Hi Hy'); [reflexivity|]. rewrite Ei. reflexivity.
      + simpl in Hd.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env bL v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (wide_template_looseness (depth n)) n (le_n _) Hn').
        destruct (proj1 (wide_template_instances (depth n)) n (le_n _) Hn') as [Hf Hb].
        assert (Hio: instantiate_ownership b o = o) by (destruct o; first [reflexivity|discriminate Ho]).
        assert (Hob: ownership_bound b o = true) by (destruct o; first [reflexivity|discriminate Ho]).
        assert (Hinst: forall w, instantiate env b (TypeArgument w o (instantiate env bS n))
            = TypeArgument w o (instantiate env b (instantiate env bS n))).
        { intros w. assert (Ha: argument_wfrag env (TypeArgument w o (instantiate env bS n)) = true) by exact (wtfrag_ktfrag env _ (wfrag_wtfrag env _ Hf)).
          assert (Hba: bound_in env b d [] (TypeArgument w o (instantiate env bS n)) = true)
              by (cbn [bound_in]; rewrite Hob, Hb; reflexivity).
          destruct (wide_argument env wf b d Hbf _ Ha Hba) as [w' [o' [n' [E [Ei _]]]]].
          injection E as <- <- <-. rewrite Ei, Hio. reflexivity. }
        destruct (mentions_loosely_bound bS n); [destruct v; cbn beta iota|];
            first [ rewrite Hinst, (IHt n ltac:(lia) Hn'); reflexivity
                  | cbn [instantiate]; rewrite Hio; reflexivity ].
Qed.

End Templates.

Lemma wide_supertype_arguments_commute: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> argument_wfrag env y = true /\ bound_in env b d [] y = true) ->
    parameterized_supertype_arguments env sub (map (instantiate env b) ys) super
        = map (instantiate env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) ->
        argument_wfrag env a = true /\ bound_in env b d [] a = true.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      apply (proj2 (wide_template_commutes sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr].
    - intros a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      apply (proj2 (wide_template_instances sub ys Hl Hys (argument_depth r))); [lia|apply Ht, Hr].
Qed.

End WideTemplates.

Section WideHelpers.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates_on env declared.
Variable b: Bindings.

(* What unify never rejects of ground types, it accepts *)
Lemma ground_accepts: forall t y, ground env t = true -> ground env y = true -> never_fails env t y ->
    exists n, unify env n t y (Ongoing []) = Some (Ongoing []).
Proof.
    intros t y HD Hy H. exact (accepts env wf declared declared_wf terminates y t
        (ground_of_fragment env declared y Hy) (ground_of_fragment env declared t HD) H).
Qed.

Lemma ground_trans: forall n1 n2 x y z, ground env x = true -> ground env y = true -> ground env z = true ->
    unify env n1 y x (Ongoing []) = Some (Ongoing []) -> unify env n2 z y (Ongoing []) = Some (Ongoing []) ->
    exists n, unify env n z x (Ongoing []) = Some (Ongoing []).
Proof.
    intros n1 n2 x y z HX HY HZ H1 H2.
    destruct (ground_of_fragment env declared x HX) as [gX rX]. destruct (ground_of_fragment env declared y HY) as [gY rY].
    destruct (ground_of_fragment env declared z HZ) as [gZ rZ].
    assert (A1: is_assignable_to env n1 x y = Some true) by (unfold is_assignable_to, empty_unification; rewrite H1; reflexivity).
    assert (A2: is_assignable_to env n2 y z = Some true) by (unfold is_assignable_to, empty_unification; rewrite H2; reflexivity).
    destruct (transitivity_terminating env wf declared declared_wf terminates n1 n2 x y z
        gX gY gZ rX rY rZ A1 A2) as [n Hf].
    exists n. unfold is_assignable_to, empty_unification in Hf.
    destruct (unify env n z x (Ongoing [])) as [[u|]|] eqn:E; try discriminate Hf.
    pose proof (ground_keeps env wf n z x [] u HZ HX E) as ->. reflexivity.
Qed.

Definition class_shaped_target (D: EType): Prop :=
    match D with RootResolved _ _ _ | Nullable (RootResolved _ _ _) => True | _ => False end.

Lemma remut_class_target: forall t, class_shaped_target t -> remut t t.
Proof.
    intros [md cd ad|[md cd ad| | | | | |]| | | | |] H; try contradiction; [left|right]; exists md, md, cd, ad; split; reflexivity.
Qed.

Lemma remut_with_mutability_class: forall m0 m1 c args, remut (RootResolved m1 c args) (with_mutability env m0 (RootResolved m1 c args)).
Proof. intros m0 m1 c args. left. do 2 eexists. exists c, args. split; reflexivity. Qed.

(* Of the same class, of a mutability below its own, a class type is taken where it is *)
Lemma ground_accepts_lower: forall n t x m s s', ground env t = true -> ground env x = true -> is_class x = true ->
    class_shaped_target t -> Model.is_subtype_of m (assignment_mutability env x) = true ->
    unify env n t x (Ongoing s) = Some (Ongoing s') -> unify env n t (with_mutability env m x) (Ongoing s) = Some (Ongoing s').
Proof.
    intros n t x m s s' HD Hx Hc Hshape Hk H.
    pose proof (ground_mutability env wf n t x s s' HD Hx H) as Hm.
    destruct x as [mx cx ax| | | | | |]; try discriminate Hc.
    apply (unify_remut env n t t (RootResolved mx cx ax) _ s s' (remut_class_target t Hshape) (remut_with_mutability_class m mx cx ax));
        [|exact H].
    simpl in Hm, Hk |- *. destruct (is_const (declaration_of env cx)); [exact Hm|exact (mutability_subtype_trans _ _ _ Hk Hm)].
Qed.

(* A type that never rejects a component of an intersection of class types, never rejects the
   intersection *)
Lemma ground_never_fails_into_intersection: forall t ys y, class_shaped_target t -> In y ys -> is_class y = true ->
    never_fails env t y -> never_fails env t (Intersection ys).
Proof.
    intros t ys y HD Hin Hy H. apply never_fails_step. intros f s.
    destruct t as [m c args|[m c args| | | | | |]| | | | |]; try contradiction.
    - exact (flipped_never_fails env f _ ys s y Hin (H f s)).
    - change (unify env (S f) (Nullable (RootResolved m c args)) (Intersection ys) (Ongoing s))
          with (unify env f (RootResolved m c args) (without_null env (Intersection ys)) (Ongoing s)).
      rewrite (without_null_not_nullable_intersection env ys
          (intersection_not_nullable env ys y Hin ltac:(destruct y; try discriminate Hy; reflexivity))).
      destruct f as [|f]; [discriminate|].
      apply (flipped_never_fails env f _ ys s y Hin).
      destruct y as [my cy argsy| | | | | |]; try discriminate Hy.
      pose proof (H (S f) s) as H'. rewrite unify_nullable_class in H'. exact H'.
Qed.

(* A class type, of another mutability, that each component of the assignee fits, never rejects
   what it takes *)
Lemma with_mutability_target_never_fails: forall n t y m0, ground env t = true -> is_class t = true -> ground env y = true ->
    unify env n t y (Ongoing []) = Some (Ongoing []) ->
    (forall z, In z (intersected_components y) -> Model.is_subtype_of (assignment_mutability env z) m0 = true) ->
    never_fails env (with_mutability env m0 t) y.
Proof.
    intros n t y m0 HD Hc Hy H Hk. destruct t as [md cd ad| | | | | |]; try discriminate Hc.
    assert (Hnv: no_vars (with_mutability env m0 (RootResolved md cd ad)) = true) by exact (ground_no_vars env _ HD).
    (* the class type of the other mutability takes a class type it takes, which fits *)
    assert (Hcls: forall g x, ground env x = true -> is_class x = true ->
        unify env g (RootResolved md cd ad) x (Ongoing []) = Some (Ongoing []) ->
        Model.is_subtype_of (assignment_mutability env x) m0 = true ->
        unify env g (with_mutability env m0 (RootResolved md cd ad)) x (Ongoing []) = Some (Ongoing [])).
    { intros g x Hx Hcx E Hxk. destruct x as [mx cx ax| | | | | |]; try discriminate Hcx.
      apply (unify_remut env g _ _ _ _ [] [] (remut_with_mutability_class m0 md cd ad) (remut_class_target (RootResolved mx cx ax) I)); [|exact E].
      pose proof (ground_mutability env wf g _ _ [] [] HD Hx E) as Hm.
      simpl in Hm |- *. destruct (is_const (declaration_of env cd)); [exact Hm|exact Hxk]. }
    destruct n as [|n]; [discriminate H|].
    destruct (ground_cases env y Hy) as [[m [z [args ->]]]|[[m [z [args ->]]]|[[ys [-> [_ Hys]]]|[ys [-> _]]]]].
    - exact (success_never_fails env wf _ _ _ [] Hnv (ground_no_vars env _ Hy)
          (Hcls (S n) _ Hy eq_refl H (Hk _ (or_introl eq_refl)))).
    - rewrite unify_class_nullable in H. discriminate H.
    - destruct (intersection_flipped_unify_found env n _ ys [] [] H) as [z [Hin Hu]].
      destruct (Hys z Hin) as [Hcc Hgc].
      pose proof (Hcls n z Hgc Hcc Hu (Hk z Hin)) as Hc'.
      pose proof (success_never_fails env wf _ _ _ [] Hnv (ground_no_vars env _ Hgc) Hc') as Hnf.
      apply never_fails_step. intros f' s.
      exact (flipped_never_fails env f' _ ys s z Hin (Hnf f' s)).
    - rewrite unify_class_nullable in H. discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The types instantiated                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* No type variables in the types of the wide fragment *)


Lemma kept_no_vars: forall t, ktfrag env t = true -> no_vars t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (ktfrag_cases env t H) as [Hwt|[[cs [-> Hk']]|[cs [-> Hk']]]].
    2,3: destruct (kcomponents_facts env cs Hk') as [_ [Hc _]]; simpl; apply forallb_forall; intros c Hin;
         pose proof (esize_in cs c Hin) as Hs;
         apply (IH (esize c)); [simpl in *; lia|reflexivity|exact (wtfrag_ktfrag env c (wfrag_wtfrag env c (proj2 (Hc c Hin))))].
    destruct (wtfrag_cases env t Hwt) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[[m_bot ->]|[[m [c [args [-> Ht']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + simpl. apply forallb_forall. intros a Hin. pose proof (Hargs a Hin) as Ha. pose proof (esize_in args a Hin) as Hs.
        destruct a as [| | | |v o n| |]; try discriminate Ha. simpl in Ha, Hs |- *.
        apply (IH (esize n)); [simpl; lia|reflexivity|exact Ha].
      + reflexivity.
      + exact (IH (esize (RootResolved m c args)) ltac:(simpl; lia) (RootResolved m c args) eq_refl
            (wtfrag_ktfrag env _ (wfrag_wtfrag env _ Ht'))).
      + destruct g as [gm nn p [|v vs]]; [reflexivity|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv].
      + destruct g as [gm nn p [|v vs]]; [reflexivity|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv].
    - destruct (wcomponents_facts env cs Hcs) as [_ Hc]. simpl. apply forallb_forall. intros c Hin.
      pose proof (esize_in cs c Hin) as Hs.
      apply (IH (esize c)); [simpl; lia|reflexivity|exact (wtfrag_ktfrag env c (wfrag_wtfrag env c (proj2 (Hc c Hin))))].
    - destruct (wcomponents_facts env cs Hcs) as [_ Hc]. simpl. apply forallb_forall. intros c Hin.
      pose proof (esize_in cs c Hin) as Hs.
      apply (IH (esize c)); [simpl; lia|reflexivity|exact (wtfrag_ktfrag env c (wfrag_wtfrag env c (proj2 (Hc c Hin))))].
Qed.

Lemma wide_no_vars: forall t, wtfrag env t = true -> no_vars t = true.
Proof. intros t H. exact (kept_no_vars t (wtfrag_ktfrag env t H)). Qed.

Lemma no_vars_keeps: forall n t a s s', no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s') -> s' = s.
Proof.
    intros n t a s s' Ht Ha H. pose proof (unify_free env wf n t a s s _ Ht Ha H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

(* What a nullable target unifies the type in it with *)
Definition nullable_assignee (a: EType): EType :=
    match a with
    | Nullable n => n
    | Generic g => Generic (narrow_ref env g)
    | Intersection _ => without_null env a
    | _ => a
    end.

Lemma unify_nullable_step: forall n t0 a s, (match a with TypeArgument _ _ _ | TypeVariable _ => False | _ => True end) ->
    unify env (S n) (Nullable t0) a (Ongoing s) = unify env n t0 (nullable_assignee a) (Ongoing s).
Proof. intros n t0 [| |[]| | | |] s H; try contradiction; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* ofComponents of ground types                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gof: forall t, ground env t = true -> of_fragment env declared t.
Proof. intros t H. exact (ground_of_fragment env declared t H). Qed.

Let btrans := below_trans env wf declared declared_wf terminates.
Let brefl := below_refl env wf declared declared_wf terminates.
Let bcomponent := intersection_below_component env wf declared declared_wf terminates.
Let binter := below_intersection_of env wf declared declared_wf terminates.
Let bcomponents := below_of_components env wf declared declared_wf terminates.

(* ... and below each of them, without null *)
Lemma below_flat_component: forall zs z, zs <> [] -> (forall z, In z zs -> flat_ground env z) -> In z zs ->
    below env (flat_intersection env zs) (without_null env z).
Proof.
    intros zs z Hne Hz Hin. destruct (flat_intersection_ground env wf zs Hne Hz) as [HN [_ Hys]].
    destruct (flat_without_null env z (Hz z Hin)) as [Hgw Hcw].
    assert (Hk: In (with_mutability env (fold_left intersect_mutability (map (assignment_mutability env) zs) readonly) (without_null env z))
        (intersected_components (flat_intersection env zs))).
    { unfold flat_intersection. cbn [intersected_components]. apply in_map_iff. exists z. split; [reflexivity|exact Hin]. }
    destruct (Hys _ Hk) as [Hgk _].
    apply (btrans _ _ _ (gof _ HN) (gof _ Hgk) (gof _ Hgw)).
    - unfold flat_intersection in HN, Hk |- *. cbn [intersected_components] in Hk. exact (bcomponent _ _ (gof _ HN) Hk).
    - destruct (brefl _ (gof _ Hgw)) as [f Hf]. exists f. apply (ground_accepts_lower f); [exact Hgw|exact Hgw|exact Hcw| | |exact Hf].
      + destruct (without_null env z); try discriminate Hcw. exact I.
      + rewrite (without_null_keeps_assignment_mutability env ranked z). apply fold_intersect_below_element. apply in_map, Hin.
Qed.

Lemma below_without_null: forall y, ground env y = true -> below env (without_null env y) y.
Proof.
    intros y Hy. destruct (is_nullable env y) eqn:En.
    2: rewrite (ground_non_null_without_null env y Hy En); exact (brefl _ (gof _ Hy)).
    pose proof (ground_without_null env _ Hy) as Hw. destruct (brefl _ (gof _ Hw)) as [f Hf]. exists (S f).
    destruct (ground_cases env y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ws [-> _]]|[ws [-> _]]]]].
    - discriminate En.
    - rewrite (ground_nullable_target env f _ _ _ Hw), (ground_without_null_idempotent env _ Hy). exact Hf.
    - rewrite (ground_intersection_not_nullable env ws (or_introl Hy)) in En. discriminate En.
    - assert (E: without_null env (Nullable (Intersection ws)) = Intersection ws).
      { change (without_null env (Nullable (Intersection ws))) with (without_null env (Intersection ws)).
        exact (without_null_not_nullable_intersection env ws (ground_intersection_not_nullable env ws (or_intror Hy))). }
      rewrite (ground_nullable_target env f _ _ _ Hw), (ground_without_null_idempotent env _ Hy). rewrite E in Hf |- *. exact Hf.
Qed.

Lemma below_nullable_both: forall x t, below env x t -> below env (Nullable x) (Nullable t).
Proof. intros x t [f Hf]. exists (S f). rewrite (unify_nullable_step f t (Nullable x) [] I). exact Hf. Qed.

(* A nullable target takes what it takes without null *)
Lemma below_without_null_assignee: forall y A, ground env y = true -> ground env A = true -> is_nullable env y = true ->
    below env A y -> below env (without_null env A) y.
Proof.
    intros y A Hy HA Hn [[|f] Hf]; [discriminate Hf|].
    destruct (ground_cases env y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ws [-> _]]|[ws [-> _]]]]];
        [discriminate Hn| |rewrite (ground_intersection_not_nullable env ws (or_introl Hy)) in Hn; discriminate Hn|];
        exists (S f); rewrite (ground_nullable_target env f _ _ _ (ground_without_null env _ HA)), (ground_without_null_idempotent env _ HA);
        rewrite (ground_nullable_target env f _ _ _ HA) in Hf; exact Hf.
Qed.

(* ofComponents of the components of ground types is below each of them *)
Lemma of_components_below: forall ys y, 2 <= length ys -> (forall y, In y ys -> ground env y = true) -> In y ys ->
    below env (of_components env (flat_map intersected_components ys)) y.
Proof.
    intros ys y Hl Hys Hin.
    assert (Hz: forall z, In z (flat_map intersected_components ys) -> flat_ground env z)
        by (intros z Hz; exact (flat_ground_components env ys z Hys Hz)).
    assert (Hsub: forall z, In z (intersected_components y) -> In z (flat_map intersected_components ys))
        by (intros z Hz'; apply in_flat_map; exists y; split; assumption).
    assert (Hlz: 2 <= length (flat_map intersected_components ys)) by (pose proof (flat_length env ys Hys); lia).
    set (zs := flat_map intersected_components ys) in *. clearbody zs.
    assert (Hne: zs <> []) by (destruct zs; [simpl in Hlz; lia|discriminate]).
    destruct (flat_intersection_ground env wf zs Hne Hz) as [HN [HnN _]].
    pose proof (Hys y Hin) as Hy.
    assert (Hb: forall z, In z (intersected_components y) -> below env (flat_intersection env zs) (without_null env z))
        by (intros z Hz'; exact (below_flat_component zs z Hne Hz (Hsub z Hz'))).
    (* below y without null *)
    assert (HbW: below env (flat_intersection env zs) (without_null env y)).
    { destruct (ground_cases env y Hy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ws [-> [_ Hws]]]|[ws [-> [_ Hws]]]]]].
      - exact (Hb _ (or_introl eq_refl)).
      - exact (Hb _ (or_introl eq_refl)).
      - rewrite (without_null_not_nullable_intersection env ws (ground_intersection_not_nullable env ws (or_introl Hy))).
        apply (binter _ _ (gof _ HN) (gof _ Hy) I). intros w Hw. pose proof (Hb w Hw) as Hbw.
        destruct (Hws w Hw) as [Hcw _]. destruct w; try discriminate Hcw. exact Hbw.
      - change (without_null env (Nullable (Intersection ws))) with (without_null env (Intersection ws)).
        rewrite (without_null_not_nullable_intersection env ws (ground_intersection_not_nullable env ws (or_intror Hy))).
        apply (binter _ _ (gof _ HN) (gof _ (ground_nullable_inner env _ Hy)) I). intros w Hw.
        pose proof (Hb (Nullable w) (in_map _ _ _ Hw)) as Hbw.
        destruct (Hws w Hw) as [Hcw _]. destruct w; try discriminate Hcw. exact Hbw. }
    destruct (forallb (is_nullable env) zs) eqn:Ez.
    - rewrite (proj2 (ground_of_components_shape env zs Hlz Hz) Ez).
      (* y is nullable, as its components are *)
      destruct (ground_cases env y Hy) as [[m [c [args Ey]]]|[[m [c [args Ey]]]|[[ws [Ey [Hwne Hws]]]|[ws [Ey _]]]]]; subst y.
      + exfalso. rewrite forallb_forall in Ez. pose proof (Ez _ (Hsub _ (or_introl eq_refl))) as E. discriminate E.
      + exact (below_nullable_both _ _ HbW).
      + exfalso. destruct ws as [|w ws']; [contradiction|]. rewrite forallb_forall in Ez.
        pose proof (Ez w (Hsub w (or_introl eq_refl))) as E. destruct (Hws w (or_introl eq_refl)) as [Hcw _].
        destruct w; try discriminate Hcw. discriminate E.
      + apply below_nullable_both.
        change (without_null env (Nullable (Intersection ws))) with (without_null env (Intersection ws)) in HbW.
        rewrite (without_null_not_nullable_intersection env ws (ground_intersection_not_nullable env ws (or_intror Hy))) in HbW.
        exact HbW.
    - rewrite (proj1 (ground_of_components_shape env zs Hlz Hz) Ez).
      exact (btrans _ (without_null env y) _ (gof _ HN) (gof _ (ground_without_null env _ Hy)) (gof _ Hy) HbW (below_without_null y Hy)).
Qed.

(* What is below each of some ground types is below ofComponents of their components *)
Lemma below_of_components_ground: forall A ys, ground env A = true -> 2 <= length ys ->
    (forall y, In y ys -> ground env y = true /\ below env A y) -> below env A (of_components env (flat_map intersected_components ys)).
Proof.
    intros A ys HA Hl Hys. destruct (is_nullable env A) eqn:En.
    2: exact (proj1 (bcomponents A ys (gof _ HA) En Hl (fun y Hy => conj (gof _ (proj1 (Hys y Hy))) (proj2 (Hys y Hy))))).
    (* of a nullable A, each of them is nullable, and so is the intersection *)
    assert (Hyn: forall y, In y ys -> is_nullable env y = true).
    { intros y Hy. destruct (Hys y Hy) as [Hgy [f Hf]]. destruct (is_nullable env y) eqn:Eny; [reflexivity|].
      rewrite (ground_non_null env f y A [] [] Hgy HA Eny Hf) in En. discriminate En. }
    destruct (bcomponents (without_null env A) ys (gof _ (ground_without_null env _ HA)) (ground_without_null_not_nullable env A HA) Hl
        (fun y Hy => conj (gof _ (proj1 (Hys y Hy)))
            (below_without_null_assignee y A (proj1 (Hys y Hy)) HA (Hyn y Hy) (proj2 (Hys y Hy))))) as [Hb _].
    pose proof (fun y Hy => proj1 (Hys y Hy)) as Hgys.
    assert (Hz: forall z, In z (flat_map intersected_components ys) -> flat_ground env z)
        by (intros z Hz; exact (flat_ground_components env ys z Hgys Hz)).
    assert (Hlz: 2 <= length (flat_map intersected_components ys)) by (pose proof (flat_length env ys Hgys); lia).
    assert (Ez: forallb (is_nullable env) (flat_map intersected_components ys) = true).
    { apply forallb_forall. intros z Hz'. apply in_flat_map in Hz'. destruct Hz' as [y [Hy Hzy]].
      pose proof (Hyn y Hy) as Hny. pose proof (Hgys y Hy) as Hgy.
      destruct (ground_cases env y Hgy) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ws [-> _]]|[ws [-> _]]]]];
          cbn [intersected_components] in Hzy.
      - discriminate Hny.
      - destruct Hzy as [<-|[]]. reflexivity.
      - rewrite (ground_intersection_not_nullable env ws (or_introl Hgy)) in Hny. discriminate Hny.
      - apply in_map_iff in Hzy. destruct Hzy as [w [<- _]]. reflexivity. }
    rewrite (proj2 (ground_of_components_shape env _ Hlz Hz) Ez) in Hb |- *.
    destruct Hb as [[|f] Hf]; [discriminate Hf|]. exists (S f).
    rewrite (ground_nullable_target env f _ _ _ HA).
    rewrite (ground_nullable_target env f _ _ _ (ground_without_null env _ HA)), (ground_without_null_idempotent env _ HA) in Hf. exact Hf.
Qed.

Lemma without_null_of_components_ground: forall zs, 2 <= length zs -> (forall z, In z zs -> flat_ground env z) ->
    without_null env (of_components env zs) = flat_intersection env zs.
Proof.
    intros zs Hl Hz. assert (Hne: zs <> []) by (destruct zs; [simpl in Hl; lia|discriminate]).
    destruct (flat_intersection_ground env wf zs Hne Hz) as [_ [HnN _]].
    destruct (forallb (is_nullable env) zs) eqn:E.
    - rewrite (proj2 (ground_of_components_shape env zs Hl Hz) E).
      change (without_null env (Nullable (flat_intersection env zs))) with (without_null env (flat_intersection env zs)).
      exact (without_null_unchanged env _ HnN).
    - rewrite (proj1 (ground_of_components_shape env zs Hl Hz) E). exact (without_null_unchanged env _ HnN).
Qed.

(* What a class type takes, each component of it is of no more mutability than the class type *)
Lemma ground_class_components_mutability: forall n t y, ground env t = true -> is_class t = true -> ground env y = true ->
    unify env n t y (Ongoing []) = Some (Ongoing []) ->
    forall x, In x (intersected_components y) -> Model.is_subtype_of (assignment_mutability env x) (assignment_mutability env t) = true.
Proof.
    intros n t y HD Hc Hy H x Hin. destruct t as [md cd ad| | | | | |]; try discriminate Hc. destruct n as [|n]; [discriminate H|].
    destruct (ground_cases env y Hy) as [[m [c' [args ->]]]|[[m [c' [args ->]]]|[[ys [-> [_ Hys]]]|[ys [-> _]]]]].
    - destruct Hin as [<-|[]]. exact (ground_mutability env wf (S n) _ _ [] [] HD Hy H).
    - rewrite unify_class_nullable in H. discriminate H.
    - destruct (intersection_flipped_unify_found env n _ ys [] [] H) as [y' [Hy' Hu]].
      pose proof (ground_mutability env wf n _ _ [] [] HD (proj2 (Hys y' Hy')) Hu) as Hm.
      pose proof (Fragment.intersection_uniform env ys (ground_gfrag env _ Hy)) as Hun.
      cbn [intersected_components] in Hin. rewrite (Hun x Hin), <- (Hun y' Hy'). exact Hm.
    - rewrite unify_class_nullable in H. discriminate H.
Qed.

End WideHelpers.

Section WideMain.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates_on env declared.
Variable b: Bindings.
Variable d0: nat.
Hypothesis Hbf: bindings_in_fragment env b.


(* A type, instantiated, takes the instance of a type that it takes *)
Definition wide_claim (n: nat) (t a: EType): Prop :=
    forall u, unify env n t a (Ongoing []) = Some (Ongoing u) ->
    exists f, unify env f (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []).

Definition types_claim (n: nat): Prop :=
    forall t a, ktfrag env t = true -> ktfrag env a = true -> bound_in env b d0 [] t = true -> bound_in env b d0 [] a = true -> wide_claim n t a.

(* The same, of the types of the wide fragment *)
Definition wide_types_claim (n: nat): Prop :=
    forall t a, wtfrag env t = true -> wtfrag env a = true -> bound_in env b d0 [] t = true -> bound_in env b d0 [] a = true -> wide_claim n t a.

Lemma wide_types_claim_of: forall n, types_claim n -> wide_types_claim n.
Proof. intros n H t a Ht Ha. exact (H t a (wtfrag_ktfrag env t Ht) (wtfrag_ktfrag env a Ha)). Qed.

Definition arguments_claim (n: nat): Prop :=
    forall t a, argument_wfrag env t = true -> argument_wfrag env a = true -> bound_in env b d0 [] t = true -> bound_in env b d0 [] a = true -> wide_claim n t a.

Lemma inst_facts: forall t, wtfrag env t = true -> bound_in env b d0 [] t = true ->
    ground env (instantiate env b t) = true /\ (is_nullable env t = false -> is_nullable env (instantiate env b t) = false)
    /\ (is_component_shape env t = true -> is_class (instantiate env b t) = true).
Proof.
    intros t Ht Hb. destruct (wide_instance env wf b d0 Hbf t (wtfrag_ktfrag env t Ht) Hb) as [Hg [_ [_ [_ [Hn Hc]]]]]. exact (conj Hg (conj Hn Hc)).
Qed.

(* ... of the types of generic code *)
Lemma kinst_facts: forall t, ktfrag env t = true -> bound_in env b d0 [] t = true ->
    ground env (instantiate env b t) = true /\ (is_nullable env t = false -> is_nullable env (instantiate env b t) = false)
    /\ (is_component_shape env t = true -> is_class (instantiate env b t) = true).
Proof.
    intros t Ht Hb. destruct (wide_instance env wf b d0 Hbf t Ht Hb) as [Hg [_ [_ [_ [Hn Hc]]]]]. exact (conj Hg (conj Hn Hc)).
Qed.

Lemma wtfrag_nullable_inner: forall t0, wtfrag env (Nullable t0) = true -> wtfrag env t0 = true.
Proof.
    intros [m c args|n|g|me msg|v o n|g|cs] H; try discriminate H; exact H.
Qed.

Lemma generic_of_wtfrag: forall g, wtfrag env (Generic g) = true -> generic_sfrag env g.
Proof.
    intros g H. change (sfrag env (Generic g) = true) in H. apply (sfrag_generic_iff env wf) in H. exact H.
Qed.

(* An intersection, instantiated *)
Lemma inst_intersection: forall cs, wcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true ->
    instantiate env b (Intersection cs) = Intersection (map (with_mutability env (common_mutability env (map (instantiate env b) cs))) (map (instantiate env b) cs))
    /\ forall C, In C cs -> ground env (instantiate env b C) = true /\ is_class (instantiate env b C) = true.
Proof.
    intros cs Hcs Hb. destruct (wcomponents_facts env cs Hcs) as [Hl Hc].
    assert (Hall: forall C, In C cs -> ground env (instantiate env b C) = true /\ is_class (instantiate env b C) = true).
    { intros C Hin. destruct (Hc C Hin) as [Hsh Hwc].
      destruct (inst_facts C (wfrag_wtfrag env C Hwc) (bound_in_component env b d0 [] cs C Hb Hin)) as [Hg [_ Hcl]].
      exact (conj Hg (Hcl Hsh)). }
    split; [|exact Hall].
    change (instantiate env b (Intersection cs)) with (intersect_instances env (map (instantiate env b) cs)).
    rewrite intersect_classes by (intros y Hy; apply in_map_iff in Hy; destruct Hy as [C [<- Hin]]; apply (Hall C Hin)).
    apply of_class_types; [rewrite length_map; exact Hl|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [C [<- Hin]]. apply (Hall C Hin).
Qed.

Lemma intersection_ground: forall cs, wcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true -> forall y,
    In y (map (with_mutability env (common_mutability env (map (instantiate env b) cs))) (map (instantiate env b) cs)) ->
    ground env y = true /\ is_class y = true.
Proof.
    intros cs Hcs Hb y Hy. destruct (inst_intersection cs Hcs Hb) as [_ Hall].
    apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
    destruct (Hall c Hin) as [Hg Hcl]. exact (ground_with_mutability env _ _ Hcl Hg).
Qed.

(* The instance of an intersection, as ofComponents makes it, is of the fragment of Fragment.v *)
Lemma intersection_instance_gfrag: forall cs, wcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true ->
    gfrag env (Intersection (map (with_mutability env (common_mutability env (map (instantiate env b) cs))) (map (instantiate env b) cs))) = true.
Proof.
    intros cs Hcs Hb. destruct (inst_intersection cs Hcs Hb) as [_ Hall]. destruct (wcomponents_facts env cs Hcs) as [Hl _].
    set (ys := map (instantiate env b) cs).
    assert (Hys: forall y, In y ys -> is_class y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. exact (proj2 (Hall c Hin)). }
    pose proof (common_classes_uniform env ys ltac:(unfold ys; destruct cs; [simpl in Hl; lia|discriminate]) Hys) as Hu.
    apply (Fragment.make_intersection_gfrag env).
    - unfold ys. destruct cs as [|c1 cs']; simpl in Hl |- *; [lia|discriminate].
    - intros y Hy. destruct (intersection_ground cs Hcs Hb y Hy) as [Hg Hcl].
      destruct y as [| | | | | |]; try discriminate Hcl. split; [reflexivity|exact (ground_gfrag env _ Hg)].
    - intros y Hy. apply internal_Mutability_dec_bl. exact (proj1 (forallb_forall _ _) Hu y Hy).
Qed.

Lemma class_non_null: forall x, is_class x = true -> is_nullable env x = false.
Proof. intros x H. destruct x; first [reflexivity|discriminate H]. Qed.

(* The instance of a type that is no intersection is a class type, nullable or not *)
Lemma inst_class_shaped: forall t, wfrag env t = true -> bound_in env b d0 [] t = true -> class_shaped_target (instantiate env b t).
Proof.
    intros t Ht Hb.
    destruct (wfrag_cases env wf t Ht) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> _]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]];
        try exact I.
    - destruct (binds_ref_some env wf b d0 [] g Hb) as [o [x [Ex [Ho [Hx _]]]]].
      rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
      destruct (fragment_cases env _ (inst_ref_in_fragment env g x (Hbf _ o x Ex))) as [[m [c [args E]]]|[m [c [args [E _]]]]];
          rewrite E; exact I.
    - destruct (binds_ref_some env wf b d0 [] g Hb) as [o [x [Ex [Ho [Hx _]]]]].
      change (instantiate env b (Nullable (Generic g))) with (rewrap_nullable (instantiate env b (Generic g))).
      rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
      destruct (fragment_cases env _ (in_fragment_rewrap env _ (inst_ref_in_fragment env g x (Hbf _ o x Ex))))
          as [[m [c [args E]]]|[m [c [args [E _]]]]]; rewrite E; exact I.
Qed.

(* An intersection whose components keep their nullability, instantiated: ofComponents of the
   components of the instances of them, ground *)
Lemma kept_instance: forall cs, kcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true ->
    instantiate env b (Intersection cs) = of_components env (flat_map intersected_components (map (instantiate env b) cs))
    /\ 2 <= length (map (instantiate env b) cs)
    /\ (forall y, In y (map (instantiate env b) cs) -> ground env y = true)
    /\ ground env (instantiate env b (Intersection cs)) = true.
Proof.
    intros cs Hcs Hb. destruct (kcomponents_facts env cs Hcs) as [Hl [Hc _]].
    assert (Hys: forall y, In y (map (instantiate env b) cs) -> ground env y = true).
    { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]].
      exact (proj1 (inst_facts c (wfrag_wtfrag env c (proj2 (Hc c Hin))) (bound_in_component env b d0 [] cs c Hb Hin))). }
    assert (Heq: instantiate env b (Intersection cs) = of_components env (flat_map intersected_components (map (instantiate env b) cs))).
    { change (instantiate env b (Intersection cs)) with (intersect_instances env (map (instantiate env b) cs)).
      apply intersect_instances_plain. intros y Hy. pose proof (Hys y Hy) as Hg.
      destruct (ground_cases env y Hg) as [[? [? [? ->]]]|[[? [? [? ->]]]|[[? [-> _]]|[? [-> _]]]]]; reflexivity. }
    assert (Hl': 2 <= length (map (instantiate env b) cs)) by (rewrite length_map; exact Hl).
    split; [exact Heq|]. split; [exact Hl'|]. split; [exact Hys|]. rewrite Heq.
    apply (ground_of_components env _ Hys).
    destruct (below_of_components env wf declared declared_wf terminates bottom_type _
        (bottom_of_fragment env wf declared) eq_refl Hl'
        (fun y Hy => conj (gof env declared _ (Hys y Hy))
            (GenericArguments.below_bottom env wf declared declared_wf terminates y (gof env declared _ (Hys y Hy)))))
        as [_ [_ [Hf _]]].
    apply Hf. intros y Hy Hn. pose proof (Hys y Hy) as Hg.
    destruct (ground_cases env y Hg) as [[? [? [? ->]]]|[[? [? [? ->]]]|[[ws [-> _]]|[? [-> _]]]]]; try exact I; try discriminate Hn.
    rewrite (ground_intersection_not_nullable env ws (or_introl Hg)) in Hn. discriminate Hn.
Qed.

Lemma inst_ground: forall t, ktfrag env t = true -> bound_in env b d0 [] t = true -> ground env (instantiate env b t) = true.
Proof.
    intros t Ht Hb. destruct (ktfrag_cases env t Ht) as [Hw|[[cs [-> Hcs]]|[cs [-> Hcs]]]]; [exact (proj1 (inst_facts t Hw Hb))| |].
    - exact (proj2 (proj2 (proj2 (kept_instance cs Hcs Hb)))).
    - change (instantiate env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate env b (Intersection cs))).
      exact (ground_rewrap_ground env _ (proj2 (proj2 (proj2 (kept_instance cs Hcs Hb))))).
Qed.

(* A component of such an intersection, instantiated, is a class type, nullable or not; without null,
   a component as those of the wide fragment, whose instance is its instance without null *)
Lemma kept_component: forall y, is_kept_shape env y = true -> wfrag env y = true -> bound_in env b d0 [] y = true ->
    flat_ground env (instantiate env b y)
    /\ is_component_shape env (without_null env y) = true /\ wfrag env (without_null env y) = true
    /\ bound_in env b d0 [] (without_null env y) = true
    /\ instantiate env b (without_null env y) = without_null env (instantiate env b y).
Proof.
    intros [m d args|n|g|me msg|v o n|g|cs] Hk Hw Hb; cbn [is_kept_shape] in Hk; try discriminate Hk.
    - (* `A?` *)
      assert (Hn: is_nullable env n = false)
          by (unfold is_component_shape in Hk; apply andb_true_iff in Hk; apply negb_true_iff, (proj2 Hk)).
      assert (Hwn: wfrag env n = true) by (cbn [wfrag] in Hw; apply andb_true_iff in Hw; exact (proj2 Hw)).
      change (bound_in env b d0 [] n = true) in Hb.
      destruct (inst_facts n (wfrag_wtfrag env n Hwn) Hb) as [Hg [_ Hcl]]. pose proof (Hcl Hk) as Hcl'.
      change (without_null env (Nullable n)) with (without_null env n). rewrite (without_null_unchanged env n Hn).
      change (instantiate env b (Nullable n)) with (rewrap_nullable (instantiate env b n)).
      destruct (instantiate env b n) as [mi di ai| | | | | |]; try discriminate Hcl'. cbn [rewrap_nullable without_null].
      split; [split; [exact (ground_nullable_class env mi di ai Hg)|right; eauto]|].
      split; [exact Hk|]. split; [exact Hwn|]. split; [exact Hb|reflexivity].
    - (* a reference to a type parameter of a nullable bound *)
      pose proof (generic_of_wtfrag g Hw) as Hg.
      destruct (narrow_generic env wf b d0 [] Hbf g Hg Hb) as [Hfn [Hbn Hin]].
      pose proof (proj2 (proj2 (tfrag_without_null env wf (S (tdepth env (Generic g))) (Generic g) ltac:(lia)
          (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg))))) as Hnn.
      rewrite (without_null_generic env g) in Hnn |- *.
      split; [|split; [|split; [exact (sfrag_wfrag env wf _ Hfn)|split; [exact Hbn|]]]].
      + destruct (binds_ref_some env wf b d0 [] g Hb) as [o [x [Ex [Ho [Hx _]]]]].
        rewrite (proj1 (instantiate_exact_generic env b g o x Ex Ho Hx)).
        pose proof (inst_ref_in_fragment env g x (Hbf _ o x Ex)) as HF. split; [exact (in_fragment_ground env _ HF)|].
        destruct (fragment_cases env _ HF) as [[m [y [args E]]]|[m [y [args [E _]]]]]; rewrite E; [left; reflexivity|right; eauto].
      + unfold is_component_shape. rewrite Hnn. reflexivity.
      + rewrite <- (inst_nested_instantiate env wf b d0 [] _ (sfrag_tfrag env _ Hfn) Hbn), Hin.
        rewrite (inst_nested_instantiate env wf b d0 [] _ (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg)) Hb). reflexivity.
Qed.

(* Without null, such an intersection is one of the wide fragment, whose instance is that of it without
   null *)
Lemma kept_without_null: forall cs, kcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true ->
    ktfrag env (without_null env (Intersection cs)) = true /\ bound_in env b d0 [] (without_null env (Intersection cs)) = true
    /\ without_null env (instantiate env b (without_null env (Intersection cs))) = without_null env (instantiate env b (Intersection cs)).
Proof.
    intros cs Hcs Hb. destruct (kcomponents_facts env cs Hcs) as [Hl [Hc _]].
    assert (Hk: forall c, In c cs -> flat_ground env (instantiate env b c)
        /\ is_component_shape env (without_null env c) = true /\ wfrag env (without_null env c) = true
        /\ bound_in env b d0 [] (without_null env c) = true
        /\ instantiate env b (without_null env c) = without_null env (instantiate env b c)).
    { intros c Hin. destruct (Hc c Hin) as [Hkc Hwc]. exact (kept_component c Hkc Hwc (bound_in_component env b d0 [] cs c Hb Hin)). }
    (* each of them may be null *)
    assert (Ew: without_null env (Intersection cs) = Intersection (map (without_null env) cs)).
    { assert (Hn: forallb (is_nullable env) cs = true).
      { apply forallb_forall. intros c Hin. destruct (Hc c Hin) as [Hkc _]. destruct c; try discriminate Hkc; [reflexivity|exact Hkc]. }
      cbn [without_null]. rewrite Hn. reflexivity. }
    assert (Hw: wcomponents env (map (without_null env) cs) = true).
    { unfold wcomponents. rewrite length_map, (proj2 (Nat.leb_le _ _) Hl). apply forallb_forall. intros c' Hc'.
      apply in_map_iff in Hc'. destruct Hc' as [c [<- Hin]]. destruct (Hk c Hin) as [_ [Hsh [Hwf _]]]. rewrite Hsh, Hwf. reflexivity. }
    assert (Hbw: bound_in env b d0 [] (Intersection (map (without_null env) cs)) = true).
    { change (forallb (bound_in env b d0 []) (map (without_null env) cs) = true). apply forallb_forall. intros c' Hc'.
      apply in_map_iff in Hc'. destruct Hc' as [c [<- Hin]]. exact (proj1 (proj2 (proj2 (proj2 (Hk c Hin))))). }
    rewrite Ew. split; [exact (wtfrag_ktfrag env (Intersection (map (without_null env) cs)) Hw)|]. split; [exact Hbw|].
    (* both: the intersection of the instances without null *)
    destruct (inst_intersection _ Hw Hbw) as [Hi _].
    assert (Hys: map (instantiate env b) (map (without_null env) cs) = map (without_null env) (map (instantiate env b) cs)).
    { rewrite !map_map. apply map_ext_in. intros c Hin. exact (proj2 (proj2 (proj2 (proj2 (Hk c Hin))))). }
    assert (Hfg: forall y, In y (map (instantiate env b) cs) -> flat_ground env y)
        by (intros y Hy; apply in_map_iff in Hy; destruct Hy as [c [<- Hin]]; exact (proj1 (Hk c Hin))).
    destruct (kept_instance cs Hcs Hb) as [Heq [Hl' _]].
    assert (Hne: map (instantiate env b) cs <> []) by (destruct cs; [simpl in Hl; lia|discriminate]).
    rewrite Heq, (flat_map_singletons env _ Hfg), (without_null_of_components_ground env wf _ Hl' Hfg).
    rewrite Hi, Hys, <- (flat_intersection_eq env wf).
    exact (without_null_unchanged env _ (proj1 (proj2 (flat_intersection_ground env wf _ Hne Hfg)))).
Qed.

(* Such an intersection, instantiated: nullable where the instance of each component is, and without null
   the instance of it without null *)
Lemma kept_instance_shape: forall cs, kcomponents env cs = true -> bound_in env b d0 [] (Intersection cs) = true ->
    is_nullable env (instantiate env b (Intersection cs)) = forallb (is_nullable env) (map (instantiate env b) cs)
    /\ without_null env (instantiate env b (Intersection cs)) = instantiate env b (without_null env (Intersection cs)).
Proof.
    intros cs Hcs Hb. destruct (kept_without_null cs Hcs Hb) as [_ [Hbw Ew]]. split.
    - destruct (kcomponents_facts env cs Hcs) as [Hl [Hc _]].
      assert (Hfg: forall y, In y (map (instantiate env b) cs) -> flat_ground env y).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. destruct (Hc c Hin) as [Hkc Hwc].
        exact (proj1 (kept_component c Hkc Hwc (bound_in_component env b d0 [] cs c Hb Hin))). }
      destruct (kept_instance cs Hcs Hb) as [Heq [Hl' _]].
      assert (Hne: map (instantiate env b) cs <> []) by (destruct cs; [simpl in Hl; lia|discriminate]).
      destruct (flat_intersection_ground env wf _ Hne Hfg) as [_ [HnN _]].
      rewrite Heq, (flat_map_singletons env _ Hfg). destruct (forallb (is_nullable env) (map (instantiate env b) cs)) eqn:E.
      + rewrite (proj2 (ground_of_components_shape env _ Hl' Hfg) E). reflexivity.
      + rewrite (proj1 (ground_of_components_shape env _ Hl' Hfg) E). exact HnN.
    - destruct (kept_without_null_shape env wf cs Hcs) as [EW HwW]. rewrite EW in Hbw, Ew |- *.
      rewrite <- Ew. apply without_null_unchanged.
      destruct (inst_intersection _ HwW Hbw) as [Ei Hcls]. rewrite Ei.
      destruct (kcomponents_facts env cs Hcs) as [Hl _]. destruct cs as [|c0 cs0]; [simpl in Hl; lia|].
      destruct (Hcls (without_null env c0) (or_introl eq_refl)) as [_ Hc]. cbn [map is_nullable forallb].
      destruct (instantiate env b (without_null env c0)); try discriminate Hc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases, by the target                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

(* A nullable target: the type in it takes the assignee without null *)
Lemma wide_nullable_target: forall n t0 a, types_claim n ->
    ktfrag env (Nullable t0) = true -> ktfrag env a = true -> bound_in env b d0 [] t0 = true -> bound_in env b d0 [] a = true -> wide_claim (S n) (Nullable t0) a.
Proof.
    intros n t0 a IH Ht Ha Hbt Hba u H. pose proof (ktfrag_nullable_inner env t0 Ht) as Ht0.
    (* what the type in the target unifies with *)
    assert (Ha': ktfrag env (nullable_assignee env a) = true /\ bound_in env b d0 [] (nullable_assignee env a) = true
        /\ without_null env (instantiate env b (nullable_assignee env a)) = without_null env (instantiate env b a)).
    { destruct a as [m c args|an|ga|me msg|v o n'|g|cs]; try discriminate Ha; cbn [nullable_assignee].
      - split; [exact Ha|split; [exact Hba|reflexivity]].
      - split; [exact (ktfrag_nullable_inner env an Ha)|]. split; [exact Hba|].
        change (instantiate env b (Nullable an)) with (rewrap_nullable (instantiate env b an)). rewrite without_null_rewrap. reflexivity.
      - destruct (ktfrag_cases env _ Ha) as [Hwa|[[? [E _]]|[? [E _]]]]; [|discriminate E|discriminate E].
        pose proof (generic_of_wtfrag ga Hwa) as Hga.
        destruct (narrow_generic env wf b d0 [] Hbf ga Hga Hba) as [Hfn [Hbn Hin]].
        split; [exact (wtfrag_ktfrag env _ (wfrag_wtfrag env _ (sfrag_wfrag env wf _ Hfn)))|]. split; [exact Hbn|].
        rewrite <- (inst_nested_instantiate env wf b d0 [] _ (sfrag_tfrag env _ Hfn) Hbn), Hin.
        rewrite (inst_nested_instantiate env wf b d0 [] _ (sfrag_tfrag env _ (generic_sfrag_sfrag env wf ga Hga)) Hba).
        apply (ground_without_null_idempotent env). exact (proj1 (inst_facts _ Hwa Hba)).
      - destruct (ktfrag_cases env _ Ha) as [Hwa|[[cs' [E Hcs]]|[? [E _]]]]; [| |discriminate E].
        + rewrite (without_null_not_nullable_intersection env cs (wcomponents_not_nullable env cs Hwa)).
          split; [exact Ha|split; [exact Hba|reflexivity]].
        + injection E as <-. exact (kept_without_null cs Hcs Hba). }
    destruct Ha' as [Hwa [Hba' Hwn]].
    rewrite (unify_nullable_step env n t0 a [] ltac:(destruct a; first [exact I|discriminate Ha])) in H.
    destruct (IH t0 _ Ht0 Hwa Hbt Hba' u H) as [f Hf].
    pose proof (inst_ground t0 Ht0 Hbt) as HT0. pose proof (inst_ground _ Hwa Hba') as HA'.
    pose proof (inst_ground a Ha Hba) as HA.
    pose proof (ground_unify_without_null env f _ _ [] [] HT0 HA' Hf) as Hw.
    exists (S f). change (instantiate env b (Nullable t0)) with (rewrap_nullable (instantiate env b t0)).
    rewrite (ground_rewrap env _ HT0), (ground_nullable_target env f _ _ [] HA), <- Hwn. exact Hw.
Qed.

(* An intersection as the target: each of its components takes the assignee *)
Lemma wide_intersection_target: forall n xs a, types_claim n ->
    wcomponents env xs = true -> ktfrag env a = true -> bound_in env b d0 [] (Intersection xs) = true -> bound_in env b d0 [] a = true ->
    wide_claim (S n) (Intersection xs) a.
Proof.
    intros n xs a IH Hts Ha Hbt Hba u H. destruct (wcomponents_facts env xs Hts) as [Hl Hc].
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end).
    { destruct a; try exact I; try discriminate Ha.
      rewrite (unify_not_nullable_intersection env n xs _ [] (wcomponents_not_nullable env xs Hts)) in H. discriminate H. }
    assert (Hnv: forall c, In c xs -> is_type_variable c = false)
        by (intros c Hin; pose proof (proj1 (Hc c Hin)) as Hsh; destruct c; first [reflexivity|discriminate Hsh]).
    assert (Hne: xs <> []) by (intros ->; simpl in Hl; lia).
    pose proof (kept_no_vars env wf a Ha) as Hnva.
    destruct (intersection_target env n xs a [] u Hnv Hne Hshape
        (fun c u' Hin E => no_vars_keeps env wf n c a [] u' (wide_no_vars env wf c (wfrag_wtfrag env c (proj2 (Hc c Hin)))) Hnva E) H)
        as [_ Hall].
    (* each component, instantiated, takes the instance of the assignee *)
    assert (Hcomp: forall c, In c xs -> exists f, unify env f (instantiate env b c) (instantiate env b a) (Ongoing []) = Some (Ongoing [])).
    { intros c Hin. destruct (Hc c Hin) as [_ Hwc].
      exact (IH c a (wtfrag_ktfrag env c (wfrag_wtfrag env c Hwc)) Ha (bound_in_component env b d0 [] xs c Hbt Hin) Hba [] (Hall c Hin)). }
    destruct (inst_intersection xs Hts Hbt) as [Heq Hcs].
    pose proof (inst_ground a Ha Hba) as HA.
    (* the instance of the assignee is non-null *)
    assert (HnA: is_nullable env (instantiate env b a) = false).
    { destruct xs as [|c1 ts']; [exfalso; exact (Hne eq_refl)|].
      destruct (Hcomp c1 (or_introl eq_refl)) as [f1 H1]. destruct (Hcs c1 (or_introl eq_refl)) as [Hg1 Hcl1].
      exact (ground_non_null env f1 _ _ [] [] Hg1 HA (class_non_null _ Hcl1) H1). }
    (* the components of the instance of the assignee are of one mutability, which each component of
       the target takes *)
    assert (Hfit: forall c, In c xs -> forall y, In y (intersected_components (instantiate env b a)) ->
        Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env (instantiate env b c)) = true).
    { intros c Hin y Hy. destruct (Hcomp c Hin) as [f Hf]. destruct (Hcs c Hin) as [Hgc Hclc].
      exact (ground_class_components_mutability env wf f _ _ Hgc Hclc HA Hf y Hy). }
    rewrite Heq. apply (ground_accepts env wf declared declared_wf terminates ).
    - unfold ground. apply andb_true_iff. split.
      + exact (intersection_instance_gfrag xs Hts Hbt).
      + change (forallb no_refs (map (with_mutability env (common_mutability env (map (instantiate env b) xs))) (map (instantiate env b) xs)) = true).
        apply forallb_forall. intros y Hy. destruct (intersection_ground xs Hts Hbt y Hy) as [Hg _].
        unfold ground in Hg. apply andb_true_iff in Hg. apply Hg.
    - exact HA.
    - apply (inter_target_never_fails env wf).
      + apply forallb_forall. intros y Hy. exact (ground_no_vars env _ (proj1 (intersection_ground xs Hts Hbt y Hy))).
      + exact (ground_no_vars env _ HA).
      + destruct (ground_cases env _ HA) as [[m [d [args E]]]|[[m [d [args E]]]|[[ys [E _]]|[ys [E _]]]]];
            rewrite E in HnA |- *; first [exact I|discriminate HnA].
      + intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'.
        destruct Hy' as [c [<- Hin]]. destruct (Hcomp c Hin) as [f Hf]. destruct (Hcs c Hin) as [Hgc Hclc].
        apply (with_mutability_target_never_fails env wf f); [exact Hgc|exact Hclc|exact HA|exact Hf|].
        intros y Hy. apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros m Hm. apply in_map_iff in Hm. destruct Hm as [z [<- Hz]]. apply in_map_iff in Hz. destruct Hz as [c' [<- Hin']].
        exact (Hfit c' Hin' y Hy).
Qed.

(* A class type or a reference as the target, an intersection as the assignee: one component of it is
   taken, and so is its instance, of the common mutability *)
Lemma wide_into_intersection: forall n t cs, wide_types_claim n ->
    wtfrag env t = true -> (is_class t || is_generic t) = true -> wcomponents env cs = true ->
    bound_in env b d0 [] t = true -> bound_in env b d0 [] (Intersection cs) = true -> wide_claim (S n) t (Intersection cs).
Proof.
    intros n t cs IH Ht Hshape Hcs Hbt Hba u H.
    destruct (unify_into_components env n t cs [] u H Hshape) as [c [Hin Hc]].
    destruct (wcomponents_facts env cs Hcs) as [_ Hcomps]. destruct (Hcomps c Hin) as [_ Hwc].
    destruct (IH t c Ht (wfrag_wtfrag env c Hwc) Hbt (bound_in_component env b d0 [] cs c Hba Hin) u Hc) as [f Hf].
    destruct (inst_intersection cs Hcs Hba) as [Heq Hall]. destruct (Hall c Hin) as [Hgc Hclc].
    pose proof (proj1 (inst_facts t Ht Hbt)) as HT.
    assert (Hst: class_shaped_target (instantiate env b t)).
    { apply inst_class_shaped; [|exact Hbt].
      destruct (wtfrag_cases env t Ht) as [Hw|[[cs' [-> _]]|[cs' [-> _]]]]; [exact Hw|discriminate Hshape|discriminate Hshape]. }
    assert (Hlow: unify env f (instantiate env b t)
        (with_mutability env (common_mutability env (map (instantiate env b) cs)) (instantiate env b c)) (Ongoing []) = Some (Ongoing [])).
    { apply (ground_accepts_lower env wf f); [exact HT|exact Hgc|exact Hclc|exact Hst| |exact Hf].
      apply fold_intersect_below_element. apply in_map, in_map, Hin. }
    rewrite Heq. apply (ground_accepts env wf declared declared_wf terminates ).
    - exact HT.
    - rewrite <- Heq. exact (proj1 (inst_facts (Intersection cs) Hcs Hba)).
    - set (k := common_mutability env (map (instantiate env b) cs)) in *.
      destruct (ground_with_mutability env k _ Hclc Hgc) as [Hgk Hck].
      apply (ground_never_fails_into_intersection env _ _ (with_mutability env k (instantiate env b c)) Hst);
          [apply in_map, in_map, Hin|exact Hck|].
      exact (success_never_fails env wf f _ _ [] (ground_no_vars env _ HT) (ground_no_vars env _ Hgk) Hlow).
Qed.

(* An intersection whose components keep their nullability as the target: each of its components takes
   the assignee, which is no `X?`, as the reference among them takes none; so the instance of each takes
   its instance, and with them, the instance of the intersection does *)
Lemma wide_kept_target: forall n cs a, types_claim n ->
    kcomponents env cs = true -> ktfrag env a = true -> bound_in env b d0 [] (Intersection cs) = true -> bound_in env b d0 [] a = true ->
    wide_claim (S n) (Intersection cs) a.
Proof.
    intros n cs a IH Hks Ha Hbt Hba u H. destruct (kcomponents_facts env cs Hks) as [Hl [Hc [g [Hg _]]]].
    pose proof (kept_no_vars env wf a Ha) as Hnva.
    assert (Hnvs: forallb no_vars cs = true).
    { apply forallb_forall. intros c Hin. exact (wide_no_vars env wf c (wfrag_wtfrag env c (proj2 (Hc c Hin)))). }
    assert (Hnv: forall c, In c cs -> is_type_variable c = false).
    { intros c Hin. pose proof (proj1 (forallb_forall _ _) Hnvs c Hin) as Hv. destruct c; first [reflexivity|discriminate Hv]. }
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end).
    { destruct a as [|an| | | | |]; try exact I; first
          [ exact (ref_component_takes_no_nullable env (S n) cs an [] u g Hnvs Hg H) | discriminate Ha ]. }
    assert (Hne: cs <> []) by (intros ->; simpl in Hl; lia).
    destruct (intersection_target env n cs a [] u Hnv Hne Hshape
        (fun c u' Hin E => no_vars_keeps env wf n c a [] u' (proj1 (forallb_forall _ _) Hnvs c Hin) Hnva E) H) as [_ Hall].
    destruct (kept_instance cs Hks Hbt) as [Heq [Hl' [Hys _]]].
    rewrite Heq. apply (below_of_components_ground env wf declared declared_wf terminates ); [exact (inst_ground a Ha Hba)|exact Hl'|].
    intros y Hy. split; [exact (Hys y Hy)|]. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]].
    destruct (Hc c Hin) as [_ Hwc].
    exact (IH c a (wtfrag_ktfrag env c (wfrag_wtfrag env c Hwc)) Ha (bound_in_component env b d0 [] cs c Hbt Hin) Hba [] (Hall c Hin)).
Qed.

(* Such an intersection as the assignee of a class type or a reference: one component of it is taken,
   whose instance is above the instance of the intersection *)
Lemma wide_into_kept: forall n t cs, types_claim n ->
    ktfrag env t = true -> (is_class t || is_generic t) = true -> kcomponents env cs = true ->
    bound_in env b d0 [] t = true -> bound_in env b d0 [] (Intersection cs) = true -> wide_claim (S n) t (Intersection cs).
Proof.
    intros n t cs IH Ht Hshape Hcs Hbt Hba u H.
    destruct (unify_into_components env n t cs [] u H Hshape) as [c [Hin Hc]].
    destruct (kcomponents_facts env cs Hcs) as [_ [Hcomps _]]. destruct (Hcomps c Hin) as [_ Hwc].
    destruct (IH t c Ht (wtfrag_ktfrag env c (wfrag_wtfrag env c Hwc)) Hbt (bound_in_component env b d0 [] cs c Hba Hin) u Hc)
        as [f Hf].
    destruct (kept_instance cs Hcs Hba) as [Heq [Hl [Hys HI]]].
    destruct (of_components_below env wf declared declared_wf terminates _ _ Hl Hys (in_map _ _ _ Hin)) as [f' Hf'].
    rewrite <- Heq in Hf'.
    exact (ground_trans env wf declared declared_wf terminates f' f _ _ _ HI (Hys _ (in_map _ _ _ Hin))
        (inst_ground t Ht Hbt) Hf' Hf).
Qed.

(* A reference as the assignee, to a type parameter that another one or a class type takes: its
   instance is within its bound, instantiated, which the instance of the target takes *)
Lemma wide_via_bound: forall n t ga, wide_types_claim n ->
    wtfrag env t = true -> (is_class t || is_generic t) = true -> generic_sfrag env ga ->
    bound_in env b d0 [] t = true -> bound_in env b d0 [] (Generic ga) = true ->
    forall s, unify env n t (effective_bound env ga) (Ongoing []) = Some (Ongoing s) ->
    exists n', unify env n' (instantiate env b t) (instantiate env b (Generic ga)) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n t ga IH Ht Hshape [Hfb _] Hbt Hba s Hu.
    destruct (binds_ref_some env wf b d0 [] ga Hba) as [o [x [E [Ho [Hx [Hr Hbe]]]]]].
    pose proof (Hbf _ o x E) as HFx. pose proof (inst_ref_in_fragment env ga x HFx) as HI.
    rewrite (proj1 (instantiate_exact_generic env b ga o x E Ho Hx)).
    destruct (instance_facts env wf b d0 [] Hbf _ _ (le_n _) Hfb Hbe) as [HB _].
    pose proof (respects_unify env wf d0 [] _ _ HI HB Hr) as Hra.
    pose proof (proj1 (inst_facts t Ht Hbt)) as HT.
    pose proof (in_fragment_ground env _ HI) as HgI.
    destruct (tfrag_cases env _ Hfb) as [Hsb|[[cs [Eb Hcs]]|[cs [Eb Hcs]]]].
    - rewrite (inst_nested_instantiate env wf b d0 [] _ Hfb Hbe) in Hra.
      pose proof (wfrag_wtfrag env _ (sfrag_wfrag env wf _ Hsb)) as Hwb.
      destruct (IH t _ Ht Hwb Hbt Hbe s Hu) as [n' Hf].
      exact (ground_trans env wf declared declared_wf terminates d0 n' _ _ _ HgI
          (proj1 (inst_facts _ Hwb Hbe)) HT Hra Hf).
    - (* the bound is an intersection: through the component of it that the target takes *)
      rewrite Eb in Hu, Hra, Hbe, HB. destruct n as [|n]; [discriminate Hu|].
      destruct (unify_into_components env n t cs [] s Hu Hshape) as [c [Hin Hc]].
      destruct (components_sfrag_facts env cs Hcs) as [_ Hcomps]. destruct (Hcomps c Hin) as [Hshc Hsc].
      pose proof (wfrag_wtfrag env c (sfrag_wfrag env wf c Hsc)) as Hwc. pose proof (bound_in_component env b d0 [] cs c Hbe Hin) as Hbc.
      destruct (IH t c Ht Hwc Hbt Hbc s (unify_fuel_monotone env n (S n) _ _ _ _ ltac:(lia) Hc))
          as [n' Hf].
      assert (Hn: forall c', In c' cs -> is_nullable env (inst_nested env b c') = false).
      { intros c' Hin'. destruct (Hcomps c' Hin') as [Hsh' Hs'].
        apply (proj2 (proj2 (instance_facts env wf b d0 [] Hbf _ c' (le_n _) (sfrag_tfrag env c' Hs')
            (bound_in_component env b d0 [] cs c' Hbe Hin')))).
        apply (component_non_null env), Hsh'. }
      destruct (intersection_instance env wf b d0 [] Hbf cs Hcs Hbe Hn) as [Heq [Hcc Hcomp]].
      rewrite Heq in Hra. assert (HK: exists K', d0 = S K') by (destruct d0; [discriminate Hra|eauto]).
      destruct HK as [K' HK']. rewrite HK' in Hra.
      destruct (inter_accepts env wf K' _ _ [] [] Hcc HI Hra) as [_ [_ Hall]].
      destruct (Hcomp c Hin) as [Hfc Hm].
      pose proof (with_mutability_accepts env K' _ _ _ [] [] Hfc HI Hm (Hall _ (in_map _ _ _ (in_map _ _ _ Hin)))) as Hcx.
      rewrite (inst_nested_instantiate env wf b d0 [] c (sfrag_tfrag env c Hsc) Hbc) in Hcx.
      exact (ground_trans env wf declared declared_wf terminates K' n' _ _ _ HgI
          (proj1 (inst_facts c Hwc Hbc)) HT Hcx Hf).
    - (* a nullable bound, which a class type or a reference takes nothing of *)
      rewrite Eb in Hu. destruct n as [|n]; [discriminate Hu|].
      destruct (wtfrag_cases env t Ht) as [Hw|[[cs' [-> _]]|[cs' [-> _]]]]; [|discriminate Hshape|discriminate Hshape].
      destruct (wfrag_cases env wf t Hw) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]];
          unfold bottom_type in *; try discriminate Hshape.
      + rewrite unify_class_nullable in Hu. discriminate Hu.
      + rewrite unify_class_nullable in Hu. discriminate Hu.
      + rewrite (unify_generic_nullable env) in Hu. discriminate Hu.
Qed.

(* Two references to the same type parameter: the instances are ordered as the bounds are *)
Lemma wide_same_parameter: forall gt ga, generic_sfrag env gt -> generic_sfrag env ga ->
    bound_in env b d0 [] (Generic gt) = true -> bound_in env b d0 [] (Generic ga) = true -> param_of ga = param_of gt ->
    Model.is_subtype_of (assignment_mutability env (effective_bound env ga)) (assignment_mutability env (effective_bound env gt)) = true ->
    (negb (is_nullable env (effective_bound env ga)) || is_nullable env (effective_bound env gt)) = true ->
    exists n, unify env n (instantiate env b (Generic gt)) (instantiate env b (Generic ga)) (Ongoing []) = Some (Ongoing []).
Proof.
    intros gt ga Hgt Hga Hbt Hba Ep Hm Hn.
    destruct (binds_ref_some env wf b d0 [] gt Hbt) as [o [x [Ex [Hot [Hxt _]]]]].
    destruct (binds_ref_some env wf b d0 [] ga Hba) as [o' [x' [Ea [Hoa [Hxa [Hra Hbe]]]]]].
    rewrite Ep, Ex in Ea. injection Ea as <- <-.
    pose proof (Hbf _ o x Ex) as HFx. destruct Hga as [Hfa [Hwa _]].
    destruct (instance_facts env wf b d0 [] Hbf _ _ (le_n _) Hfa Hbe) as [HB [HmB HnB]].
    rewrite (proj1 (instantiate_exact_generic env b gt o x Ex Hot Hxt)).
    rewrite (proj1 (instantiate_exact_generic env b ga o x (eq_trans (f_equal (lookup_binding b) Ep) Ex) Hot Hxt)).
    exists (depth x).
    apply (same_parameter env wf d0 [] (depth x) gt ga x _ HFx HB); [|exact Hgt| |exact HmB|exact HnB|exact Hm|exact Hn].
    - exact (proj1 (reflexivity_with_arguments env (depth x)) x [] HFx (le_n _)).
    - apply (respects_unify env wf d0 []); [apply inst_ref_in_fragment, HFx|exact HB|exact Hra].
Qed.

Lemma forall2_uniform: forall (Q: nat -> EType -> EType -> Prop), (forall n n' x y, n <= n' -> Q n x y -> Q n' x y) ->
    forall xs ys, Forall2 (fun x y => exists n, Q n x y) xs ys -> exists d, Forall2 (Q d) xs ys.
Proof.
    intros Q Hm xs ys H. induction H as [|x y xs ys [f1 H1] _ [d HF]]; [exists 0; constructor|].
    exists (max f1 d). constructor; [apply (Hm f1); [lia|exact H1]|].
    apply (Forall2_impl_in _ _ xs ys HF). intros a c _ _ Ha. apply (Hm d); [lia|exact Ha].
Qed.

Lemma forall2_map_instances: forall d xs ys,
    Forall2 (fun a t => unify env d (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing [])) xs ys ->
    Forall2 (fun a t => unify env d t a (Ongoing []) = Some (Ongoing [])) (map (instantiate env b) xs) (map (instantiate env b) ys).
Proof. intros d xs ys H. induction H; constructor; assumption. Qed.


(* Two class types: their type arguments pairwise, those of a subclass normalized *)
Lemma wide_classes: forall n mt ct targs ma ca aargs, arguments_claim n ->
    wfrag env (RootResolved mt ct targs) = true -> wfrag env (RootResolved ma ca aargs) = true ->
    bound_in env b d0 [] (RootResolved mt ct targs) = true -> bound_in env b d0 [] (RootResolved ma ca aargs) = true ->
    wide_claim (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs).
Proof.
    intros n mt ct targs ma ca aargs IH Ht Ha Hbt Hba u H.
    pose proof (no_vars_keeps env wf _ _ _ _ _ (wide_no_vars env wf _ (wfrag_wtfrag env _ Ht))
        (wide_no_vars env wf _ (wfrag_wtfrag env _ Ha)) H) as ->.
    change (instantiate env b (RootResolved mt ct targs)) with (RootResolved mt ct (map (instantiate env b) targs)).
    change (instantiate env b (RootResolved ma ca aargs)) with (RootResolved ma ca (map (instantiate env b) aargs)).
    rewrite unify_classes in H.
    destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate H].
    destruct (Model.is_subtype_of _ _) eqn:Em; [|discriminate H].
    destruct (class_eqb ca nothing) eqn:Hcn.
    { exists 1. rewrite unify_classes, Hbase.
      rewrite (assignment_mutability_of_class env ma ca (map (instantiate env b) aargs) aargs),
          (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Em, Hcn. reflexivity. }
    assert (Hct: class_eqb ct nothing = false).
    { destruct (class_eqb ct nothing) eqn:E; [|reflexivity]. apply class_eqb_true in E. subst ct.
      rewrite (only_nothing_is_below_nothing env ca Hbase), class_eqb_refl in Hcn. discriminate Hcn. }
    destruct (wfrag_cases env wf _ Ht) as [[mt' [ct' [targs' [Heq [_ [Hlt Htargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
        try discriminate Heq; [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hct; discriminate Hct].
    destruct (wfrag_cases env wf _ Ha) as [[ma' [ca' [aargs' [Heq [_ [Hla Haargs]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[[? [Heq _]]|[? [Heq _]]]]]];
        try discriminate Heq; [injection Heq as <- <- <-|unfold bottom_type in Heq; injection Heq as _ -> _; rewrite class_eqb_refl in Hcn; discriminate Hcn].
    (* the type arguments of the assignee, normalized to the target's class, and instantiated *)
    assert (Hnorm: exists nargs,
        (if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) = nargs
        /\ (if class_eqb ca ct then map (instantiate env b) aargs
            else parameterized_supertype_arguments env ca (map (instantiate env b) aargs) ct) = map (instantiate env b) nargs
        /\ length targs = length nargs
        /\ forall a, In a nargs -> argument_wfrag env a = true /\ bound_in env b d0 [] a = true).
    { destruct (Class_eq_dec ca ct) as [<-|Hne].
      - rewrite class_eqb_refl. exists aargs. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        intros a Hin. split; [exact (Haargs a Hin)|]. exact (bound_in_root env b d0 [] _ _ _ Hba a Hin).
      - rewrite (class_eqb_false _ _ Hne).
        assert (Hys: forall y, In y aargs -> argument_wfrag env y = true /\ bound_in env b d0 [] y = true)
            by (intros y Hy; split; [apply Haargs, Hy|apply (bound_in_root env b d0 [] _ _ _ Hba y Hy)]).
        destruct (wide_supertype_arguments_commute env wf b d0 Hbf ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Hys)
            as [Hcomm Hfacts].
        exists (parameterized_supertype_arguments env ca aargs ct). split; [reflexivity|]. split; [exact Hcomm|]. split.
        + destruct (wf_supertypes_are_templates env wf ca ct Hne (class_eqb_false_neq _ _ Hcn) Hbase) as [Hlt' _].
          rewrite parameterized_supertype_arguments_eq, length_map, Hlt'. lia.
        + intros a Hin. destruct (Hfacts a Hin) as [Hw Hb']. split; [exact Hw|exact Hb']. }
    destruct Hnorm as [nargs [E1 [E2 [Hlen Hnargs]]]].
    rewrite E1 in H. unfold unify_arguments in H.
    (* the type arguments pairwise, generically *)
    assert (Hargs_nv: forall a, argument_wfrag env a = true -> no_vars a = true).
    { intros [| | | |v o n'| |] Ha'; try discriminate Ha'. exact (kept_no_vars env wf n' Ha'). }
    pose proof (pairwise_of_arguments env n targs nargs [] Hlen
        (fun t a w Hti Hai E => no_vars_keeps env wf n t a [] w (Hargs_nv t (Htargs t Hti)) (Hargs_nv a (proj1 (Hnargs a Hai))) E) H)
        as Hpairs.
    (* and instantiated *)
    assert (Hinst: Forall2 (fun a t => exists f, unify env f (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))
        nargs targs).
    { apply (Forall2_impl_in _ _ _ _ Hpairs). intros a t Hai Hti E.
      destruct (Hnargs a Hai) as [Hwa Hba'].
      exact (IH t a (Htargs t Hti) Hwa (bound_in_root env b d0 [] _ _ _ Hbt t Hti) Hba' [] E). }
    destruct (forall2_uniform (fun F a t => unify env F (instantiate env b t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))
        (fun f f' a t Hle E => unify_fuel_monotone env f f' _ _ _ _ Hle E) nargs targs Hinst) as [F HF].
    exists (S F). rewrite unify_classes, Hbase.
    rewrite (assignment_mutability_of_class env ma ca (map (instantiate env b) aargs) aargs),
        (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Em, Hcn, E2.
    unfold unify_arguments. apply (fold_of_pairs env). exact (forall2_map_instances F nargs targs HF).
Qed.

Lemma top_wide: ktfrag env top_type = true /\ bound_in env b d0 [] top_type = true
    /\ instantiate env b top_type = top_type.
Proof.
    split; [exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ (top_in_sfrag env wf)))|]. repeat split; exact I.
Qed.

Lemma bottom_wide: ktfrag env bottom_type = true /\ bound_in env b d0 [] bottom_type = true
    /\ instantiate env b bottom_type = bottom_type.
Proof. split; [exact (wfrag_wtfrag env _ (sfrag_wfrag env wf _ (bottom_in_sfrag env wf)))|]. repeat split; exact I. Qed.

(* Two type arguments *)
Lemma wide_arguments_case: forall n, types_claim n -> arguments_claim (S n).
Proof.
    intros n IH [| | | |vt ot nt| |] [| | | |va oa na| |] Ht Ha Hbt Hba u H; try discriminate Ht; try discriminate Ha.
    destruct (wide_argument env wf b d0 Hbf _ Ht Hbt) as [vt' [ot' [nt' [Et [Eit [Hwt [Hbnt [_ [_ [_ _]]]]]]]]]].
    injection Et as <- <- <-.
    destruct (wide_argument env wf b d0 Hbf _ Ha Hba) as [va' [oa' [na' [Ea [Eia [Hwa [Hbna [_ [_ [_ _]]]]]]]]]].
    injection Ea as <- <- <-.
    pose proof (kept_no_vars env wf nt Hwt) as Hnvt.
    assert (Htv: is_type_variable nt = false) by (destruct nt; first [reflexivity|discriminate Hnvt]).
    pose proof (inst_ground nt Hwt Hbnt) as HIt.
    assert (Htv': is_type_variable (instantiate env b nt) = false)
        by (pose proof (ground_no_vars env _ HIt) as Hv; destruct (instantiate env b nt); first [reflexivity|discriminate Hv]).
    rewrite unify_type_arguments in H by exact Htv.
    destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
    rewrite Eit, Eia.
    destruct top_wide as [Hwtop [Hbtop Hitop]]. destruct bottom_wide as [Hwbot [Hbbot Hibot]].
    assert (Hown: ownership_is_assignable_to (instantiate_ownership b oa) (instantiate_ownership b ot) = true)
        by exact (instantiation_preserves_ownership_assignability b oa ot Ho).
    destruct vt, va; unfold compare_variances in H; try discriminate H.
    1: { (* both ways *)
      destruct (unify env n nt na (Ongoing [])) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
      pose proof (no_vars_keeps env wf _ _ _ _ _ Hnvt (kept_no_vars env wf na Hwa) E1) as ->.
      destruct (IH nt na Hwt Hwa Hbnt Hbna [] E1) as [f1 H1].
      destruct (IH na nt Hwa Hwt Hbna Hbnt u H) as [f2 H2].
      exists (S (max f1 f2)). rewrite unify_type_arguments by exact Htv'. rewrite Hown. unfold compare_variances.
      rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) H1).
      exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) H2). }
    all: first
        [ destruct (IH nt na Hwt Hwa Hbnt Hbna u H) as [f Hf]
        | destruct (IH na nt Hwa Hwt Hbna Hbnt u H) as [f Hf]
        | destruct (IH nt top_type Hwt Hwtop Hbnt Hbtop u H) as [f Hf]; rewrite Hitop in Hf
        | destruct (IH bottom_type nt Hwbot Hwt Hbbot Hbnt u H) as [f Hf]; rewrite Hibot in Hf ];
        exists (S f); (rewrite unify_type_arguments by exact Htv'); rewrite Hown; exact Hf.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* All the cases                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma wide_main: forall n, types_claim n /\ arguments_claim n.
Proof.
    induction n as [|n [IHt IHa]].
    { split; intros t a _ _ _ _ u H; discriminate H. }
    pose proof (wide_types_claim_of n IHt) as IHw.
    split; [|exact (wide_arguments_case n IHt)].
    intros t a Ht Ha Hbt Hba u H.
    destruct (ktfrag_cases env t Ht) as [Hwt|[[ts [-> Hts]]|[ts [-> Hts]]]].
    2: exact (wide_kept_target n ts a IHt Hts Ha Hbt Hba u H).
    2: exact (wide_nullable_target n (Intersection ts) a IHt Ht Ha Hbt Hba u H).
    destruct (wtfrag_cases env t Hwt) as [Hw|[[ts [-> Hts]]|[ts [-> Hts]]]].
    2: exact (wide_intersection_target n ts a IHt Hts Ha Hbt Hba u H).
    2: exact (wide_nullable_target n (Intersection ts) a IHt Ht Ha Hbt Hba u H).
    destruct (wfrag_cases env wf t Hw) as [[mt [ct [targs [-> _]]]]|[[m_bot ->]|[[mt [ct [targs [-> _]]]]|[[gt [-> Hgt]]|[gt [-> Hgt]]]]]].
    3,5: exact (wide_nullable_target n _ a IHt Ht Ha Hbt Hba u H).
    (* an intersection whose components keep their nullability, as the assignee of a class type or a
       reference; made nullable, they take none of it *)
    all: destruct (ktfrag_cases env a Ha) as [Hwa0|[[cs [-> Hcs]]|[cs [-> Hcs]]]];
        [|exact (wide_into_kept n _ cs IHt Ht eq_refl Hcs Hbt Hba u H)
         |first [rewrite unify_class_nullable in H; discriminate H|rewrite (unify_generic_nullable env) in H; discriminate H]].
    3: (* a reference to a type parameter *)
      { destruct (wtfrag_cases env a Hwa0) as [Hwa|[[cs [-> Hcs]]|[cs [-> _]]]].
        - destruct (wfrag_cases env wf a Hwa) as [[ma [ca [aargs [-> [Hca _]]]]]|[[m_bot ->]|[[ma [ca [aargs [-> _]]]]|[[ga [-> Hga]]|[ga [-> _]]]]]].
          + rewrite (unify_generic_root env wf), Hca in H. cbn [andb] in H. discriminate H.
          + unfold bottom_type in H. rewrite (unify_generic_root env wf) in H. rewrite class_eqb_refl in H. cbn [andb] in H.
            destruct (Model.is_subtype_of _ _); [|discriminate H].
            destruct (binds_ref_some env wf b d0 [] gt Hbt) as [o [x [Ex [Ho [Hx _]]]]].
            rewrite (proj1 (instantiate_exact_generic env b gt o x Ex Ho Hx)). exists 2.
            exact (below_all env wf [] _ 2 (inst_ref_in_fragment env gt x (Hbf _ o x Ex)) (le_n _) _).
          + rewrite (unify_generic_nullable env) in H. discriminate H.
          + rewrite (unify_generic_generic_step env wf) in H. destruct (param_eqb (param_of ga) (param_of gt)) eqn:Ep.
            * apply param_eqb_eq in Ep. destruct (_ && _) eqn:Ec in H; [|discriminate H].
              apply andb_true_iff in Ec. destruct Ec as [Hm Hn].
              exact (wide_same_parameter gt ga Hgt Hga Hbt Hba Ep Hm Hn).
            * exact (wide_via_bound n (Generic gt) ga IHw Hwt eq_refl Hga Hbt Hba u H).
          + rewrite (unify_generic_nullable env) in H. discriminate H.
        - exact (wide_into_intersection n (Generic gt) cs IHw Hwt eq_refl Hcs Hbt Hba u H).
        - rewrite (unify_generic_nullable env) in H. discriminate H. }
    (* a class type *)
    all: unfold bottom_type in *.
    all: destruct (wtfrag_cases env a Hwa0) as [Hwa|[[cs [-> Hcs]]|[cs [-> _]]]];
        [|exact (wide_into_intersection n _ cs IHw Hwt eq_refl Hcs Hbt Hba u H)
         |rewrite unify_class_nullable in H; discriminate H].
    all: destruct (wfrag_cases env wf a Hwa) as [[ma [ca [aargs [-> _]]]]|[[? ->]|[[ma [ca [aargs [-> _]]]]|[[ga [-> Hga]]|[ga [-> _]]]]]];
        unfold bottom_type in *;
        first [ rewrite unify_class_nullable in H; discriminate H
              | exact (wide_classes n _ _ _ _ _ _ IHa Hw Hwa Hbt Hba u H)
              | rewrite (unify_root_generic env) in H; exact (wide_via_bound n _ ga IHw Hwt eq_refl Hga Hbt Hba u H) ].
Qed.

End WideMain.

(*
 * The substitution lemma, intersections in type arguments included: within the wide fragment, a
 * type that is assignable to another stays so, with the type parameters in both instantiated
 * exactly, where unify terminates on the environment (unify_terminates_on, Conjectures.v)
 *)
Theorem substitution_wide: forall env declared b d fuel t a,
    wellformed env -> bounds_wellformed env declared -> unify_terminates_on env declared ->
    bindings_in_fragment env b ->
    ktfrag env t = true -> ktfrag env a = true -> bound_in env b d [] t = true -> bound_in env b d [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    exists n, is_assignable_to env n (instantiate env b a) (instantiate env b t) = Some true.
Proof.
    intros env declared b d fuel t a wf declared_wf terminates Hbf Ht Ha Hbt Hba H.
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    destruct (proj1 (wide_main env wf declared declared_wf terminates b d Hbf fuel)
        t a Ht Ha Hbt Hba u Eu) as [n Hf].
    exists n. rewrite Hf. reflexivity.
Qed.

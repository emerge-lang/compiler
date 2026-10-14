From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Generics.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Type arguments within their bounds                                                             *)
(*                                                                                                *)
(* The substitution lemmas take as a premise that every reference to a type parameter in the      *)
(* types is, instantiated, within its bound, instantiated (bound_in). This derives it from what   *)
(* Kotlin checks of type arguments: each is within the declared bound of its type parameter,      *)
(* instantiated (bound_in_derived). A reference applies a mutability and `!` to the declared      *)
(* bound (GenericTypeReference.effectiveBound; built says the references are made so).            *)
(* within_adjust shows a type below the declared bound, of no more than the mutability applied,   *)
(* below the bound with it applied, shape by shape of the declared bound: class types, references *)
(* to other type parameters, intersections, nullable or not.                                      *)
(*                                                                                                *)
(* Not so for a reference of a mutability core scalars don't have (`mut T`) to a type parameter   *)
(* bound to a core scalar, whose values are immutable whatever the mutability (see                *)
(* Substitution.v): scalar_fits leaves those out, as deep_scalar_free in SubstitutionWide.v       *)
(* leaves out intersections with components that are core scalars (roadmap items 28 and 29).      *)
(* ---------------------------------------------------------------------------------------------- *)

Section WithinBounds.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* ---------------------------------------------------------------------------------------------- *)
(* The same class type, of other mutabilities and nullabilities                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma remut_sym: forall t t', remut t t' -> remut t' t.
Proof.
    intros t t' [[m [m' [c [args [-> ->]]]]]|[m [m' [c [args [-> ->]]]]]]; [left|right]; exists m', m, c, args; split; reflexivity.
Qed.

Lemma remut_trans: forall t1 t2 t3, remut t1 t2 -> remut t2 t3 -> remut t1 t3.
Proof.
    intros t1 t2 t3 [[m1 [m2 [c [args [-> ->]]]]]|[m1 [m2 [c [args [-> ->]]]]]]
        [[m2' [m3 [c' [args' [E ->]]]]]|[m2' [m3 [c' [args' [E ->]]]]]]; try discriminate E;
        injection E as E1 E2 E3; subst; [left|right]; do 4 eexists; split; reflexivity.
Qed.

Lemma remut_without_null: forall t t', remut t t' -> remut (without_null t) (without_null t').
Proof.
    intros t t' [[m [m' [c [args [-> ->]]]]]|[m [m' [c [args [-> ->]]]]]]; left; exists m, m', c, args; split; reflexivity.
Qed.

(* Removing null from both sides of x and of a class type of x of another mutability *)
Lemma remut_derived: forall x t, in_fragment env x = true -> remut x t ->
    remut (without_null x) (without_null t).
Proof. intros x t _ H. exact (remut_without_null x t H). Qed.

Lemma remut_inst_ref: forall g x, in_fragment env x = true -> remut (without_null x) (without_null (inst_ref env g x)).
Proof.
    intros g x Hx. pose proof (remut_without_null _ _ (remut_inst_fit env g x Hx)) as H.
    unfold inst_ref. destruct (is_narrowed g); [|exact H].
    rewrite (without_null_idempotent env _ (inst_fit_in_fragment env g x Hx)). exact H.
Qed.

Lemma mutability_rewrap: forall t, in_fragment env t = true -> mutability_of env (rewrap_nullable t) = mutability_of env t.
Proof.
    intros t H. rewrite (rewrap_without_null env t H). change (mutability_of env (without_null t) = mutability_of env t).
    exact (mutability_of_without_null env t H).
Qed.

Lemma nullable_rewrap: forall t, is_nullable (rewrap_nullable t) = true.
Proof. intros [| | | | | |]; reflexivity. Qed.

(* x below a class type is below the same class type of another mutability that fits, and without
   null where that is *)
Lemma lift: forall f Y T Z (nn: bool), in_fragment env Y = true -> in_fragment env T = true -> in_fragment env Z = true ->
    remut (without_null Y) (without_null T) ->
    Model.is_subtype_of (mutability_of env Z) (mutability_of env T) = true ->
    (is_nullable T = false -> is_nullable Y = false \/ nn = true) ->
    unify env f Y Z (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' T (if nn then without_null Z else Z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f Y T Z nn HY HT HZ Hr Hm Hn H.
    pose proof (unify_without_null env f Y Z [] [] HY HZ H) as H2.
    assert (H3: unify env f (without_null T) (without_null Z) (Ongoing []) = Some (Ongoing [])).
    { apply (unify_remut env f (without_null Y) (without_null T) (without_null Z) (without_null Z) [] [] Hr
          (remut_refl env _ (in_fragment_without_null env Z HZ))); [|exact H2].
      rewrite (mutability_of_without_null env Z HZ), (mutability_of_without_null env T HT). exact Hm. }
    destruct (is_nullable T) eqn:EnT.
    - exists (S f). destruct (fragment_cases env T HT) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]]; [discriminate EnT|].
      assert (HZ': in_fragment env (if nn then without_null Z else Z) = true)
          by (destruct nn; [apply in_fragment_without_null|]; exact HZ).
      rewrite (unify_nullable_target env f _ _ [] HZ').
      replace (without_null (if nn then without_null Z else Z)) with (without_null Z)
          by (destruct nn; [symmetry; apply (without_null_idempotent env Z HZ)|reflexivity]).
      exact H3.
    - rewrite (without_null_non_null env T HT EnT) in H3. exists f. destruct nn; [exact H3|].
      destruct (Hn eq_refl) as [HnY|E]; [|discriminate E].
      rewrite (without_null_non_null env Z HZ (accepted_non_null env f Y Z [] [] HY HZ HnY H)) in H3. exact H3.
Qed.

Section Bindings.

Variable b: Bindings.
Hypothesis Hbf: bindings_in_fragment env b.

(* A class type of x of a lower mutability is below what x is below *)
Lemma cfrag_lower: forall f Y x Z, cfrag env Y = true -> in_fragment env x = true -> in_fragment env Z = true ->
    remut x Z -> Model.is_subtype_of (mutability_of env Z) (mutability_of env x) = true ->
    unify env f Y x (Ongoing []) = Some (Ongoing []) -> exists f', unify env f' Y Z (Ongoing []) = Some (Ongoing []).
Proof.
    intros f Y x Z HY Hx HZ Hr Hm H.
    assert (Hinter: forall f0 ys x Z, class_components env ys = true -> in_fragment env x = true -> in_fragment env Z = true ->
        remut x Z -> Model.is_subtype_of (mutability_of env Z) (mutability_of env x) = true ->
        unify env (S f0) (Intersection ys) x (Ongoing []) = Some (Ongoing []) ->
        unify env (S f0) (Intersection ys) Z (Ongoing []) = Some (Ongoing [])).
    { clear x Z Hx HZ Hr Hm H. intros f0 ys x Z Hys Hx' HZ' Hr' Hm' E. destruct (inter_accepts env wf f0 ys x [] [] Hys Hx' E) as [_ [Hnx Hall]].
      destruct (class_components_facts env ys Hys) as [_ Hc].
      apply (inter_takes env f0 ys Z [] Hys HZ').
      - destruct Hr' as [[m [m' [c [args [-> ->]]]]]|[m [m' [c [args [-> ->]]]]]]; [reflexivity|discriminate Hnx].
      - intros c Hin. apply (unify_remut env f0 c c x Z [] [] (remut_refl env c (proj2 (Hc c Hin))) Hr'); [|exact (Hall c Hin)].
        exact (mutability_subtype_trans _ _ _ Hm' (accepted_mutability_classes env f0 c x [] [] (proj2 (Hc c Hin)) Hx' (Hall c Hin))). }
    destruct (cfrag_cases env Y HY) as [HY'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exists f. apply (unify_remut env f Y Y x Z [] [] (remut_refl env Y HY') Hr); [|exact H].
      exact (mutability_subtype_trans _ _ _ Hm (accepted_mutability_classes env f Y x [] [] HY' Hx H)).
    - destruct f as [|f]; [discriminate H|]. exists (S f). exact (Hinter f ys x Z Hys Hx HZ Hr Hm H).
    - destruct f as [|f]; [discriminate H|]. exists (S f).
      rewrite (unify_nullable_target env f _ x [] Hx) in H. rewrite (unify_nullable_target env f _ Z [] HZ).
      destruct f as [|f]; [discriminate H|].
      apply (Hinter f ys _ _ Hys (in_fragment_without_null env x Hx) (in_fragment_without_null env Z HZ) (remut_without_null _ _ Hr));
          [|exact H].
      rewrite (mutability_of_without_null env Z HZ), (mutability_of_without_null env x Hx). exact Hm.
Qed.

(* Below the instance of a reference, of a class type of x: below the instance of another reference
   to the same type parameter, of a mutability m that fits *)
Lemma ref_lift: forall f g1 g2 x m Z (nn: bool), in_fragment env x = true -> in_fragment env Z = true ->
    given_mutability g2 = Some m -> Model.is_subtype_of (mutability_of env Z) m = true ->
    (forall Y, Y = inst_ref env g1 x \/ Y = rewrap_nullable (inst_ref env g1 x) ->
        forall T, (T = inst_ref env g2 x /\ (is_nullable T = false -> is_nullable Y = false \/ nn = true))
            \/ (T = rewrap_nullable (inst_ref env g2 x)) ->
        unify env f Y Z (Ongoing []) = Some (Ongoing []) ->
        exists f', unify env f' T (if nn then without_null Z else Z) (Ongoing []) = Some (Ongoing [])).
Proof.
    intros f g1 g2 x m Z nn Hx HZ Hg Hm Y HY T HT H.
    assert (HfY: in_fragment env Y = true)
        by (destruct HY as [->| ->]; [|apply in_fragment_rewrap]; apply inst_ref_in_fragment, Hx).
    assert (HfT: in_fragment env T = true)
        by (destruct HT as [[-> _]| ->]; [|apply in_fragment_rewrap]; apply inst_ref_in_fragment, Hx).
    assert (HwY: without_null Y = without_null (inst_ref env g1 x)) by (destruct HY as [->| ->]; [|apply without_null_rewrap]; reflexivity).
    assert (HwT: without_null T = without_null (inst_ref env g2 x))
        by (destruct HT as [[-> _]| ->]; [|apply without_null_rewrap]; reflexivity).
    assert (HmY: mutability_of env Y = mutability_of env (inst_fit env g1 x)).
    { destruct HY as [->| ->]; [|rewrite (mutability_rewrap _ (inst_ref_in_fragment env g1 x Hx))]; apply mutability_inst_ref, Hx. }
    assert (HmT: mutability_of env T = mutability_of env (inst_fit env g2 x)).
    { destruct HT as [[-> _]| ->]; [|rewrite (mutability_rewrap _ (inst_ref_in_fragment env g2 x Hx))]; apply mutability_inst_ref, Hx. }
    apply (lift f Y T Z nn HfY HfT HZ).
    - rewrite HwY, HwT. exact (remut_trans _ _ _ (remut_sym _ _ (remut_inst_ref g1 x Hx)) (remut_inst_ref g2 x Hx)).
    - rewrite HmT. pose proof (accepted_mutability_classes env f Y Z [] [] HfY HZ H) as HZY. rewrite HmY in HZY.
      pose proof (mutability_subtype_trans _ _ _ HZY (inst_fit_mutability_below env g1 x Hx)) as HZx.
      unfold inst_fit. rewrite Hg.
      destruct (with_mutability_cases env x Hx) as [Hc|Hc]; rewrite Hc; [apply intersect_mutability_greatest|]; assumption.
    - destruct HT as [[_ HT]| ->]; [exact HT|rewrite nullable_rewrap; discriminate].
    - exact H.
Qed.

(* Below a class type, below it of another mutability that fits, and without null *)
Lemma lift_class: forall f Y Z m (nn: bool), in_fragment env Y = true -> in_fragment env Z = true ->
    Model.is_subtype_of (mutability_of env Z) m = true ->
    unify env f Y Z (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' (if nn then without_null (with_mutability env m Y) else with_mutability env m Y)
        (if nn then without_null Z else Z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f Y Z m nn HY HZ Hm H. pose proof (in_fragment_with_mutability env m Y HY) as HwY.
    apply (lift f Y _ Z nn HY); [destruct nn; [apply in_fragment_without_null|]; exact HwY|exact HZ| | | |exact H].
    - replace (without_null (if nn then without_null (with_mutability env m Y) else with_mutability env m Y))
          with (without_null (with_mutability env m Y)) by (destruct nn; [symmetry; apply (without_null_idempotent env _ HwY)|reflexivity]).
      exact (remut_without_null _ _ (remut_with_mutability env m Y HY)).
    - replace (mutability_of env (if nn then without_null (with_mutability env m Y) else with_mutability env m Y))
          with (mutability_of env (with_mutability env m Y)) by (destruct nn; [symmetry; apply (mutability_of_without_null env _ HwY)|reflexivity]).
      pose proof (accepted_mutability_classes env f Y Z [] [] HY HZ H) as HZY.
      destruct (with_mutability_cases env Y HY) as [Hc|Hc]; rewrite Hc; assumption.
    - intros Hn. destruct nn; [right; reflexivity|left]. rewrite (nullable_with_mutability env m Y HY) in Hn. exact Hn.
Qed.

Lemma remut_class_instances: forall g g' x, in_fragment env x = true ->
    is_nullable (inst_ref env g x) = false -> is_nullable (inst_ref env g' x) = false ->
    remut (inst_ref env g x) (inst_ref env g' x).
Proof.
    intros g g' x Hx Hn Hn'.
    pose proof (remut_trans _ _ _ (remut_sym _ _ (remut_inst_ref g x Hx)) (remut_inst_ref g' x Hx)) as H.
    rewrite (without_null_non_null env _ (inst_ref_in_fragment env g x Hx) Hn),
        (without_null_non_null env _ (inst_ref_in_fragment env g' x Hx) Hn') in H.
    exact H.
Qed.

Lemma nullable_inst_ref: forall g x, in_fragment env x = true ->
    is_nullable (inst_ref env g x) = negb (is_narrowed g) && is_nullable x.
Proof.
    intros g x Hx. unfold inst_ref. destruct (is_narrowed g).
    - cbn [negb andb]. apply (Substitution.without_null_not_nullable env), (inst_fit_in_fragment env), Hx.
    - cbn [negb andb]. apply (nullable_inst_fit env), Hx.
Qed.

Lemma inst_fit_mutability: forall g x m, in_fragment env x = true -> given_mutability g = Some m ->
    forall k, Model.is_subtype_of k m = true -> Model.is_subtype_of k (mutability_of env x) = true ->
    Model.is_subtype_of k (mutability_of env (inst_fit env g x)) = true.
Proof.
    intros g x m Hx Hg k Hkm Hkx. unfold inst_fit. rewrite Hg.
    destruct (with_mutability_cases env x Hx) as [Hc|Hc]; rewrite Hc; [apply intersect_mutability_greatest|]; assumption.
Qed.

(*
 * What is below a type, instantiated, is below it with another mutability, of no more than what is
 * below, applied, and without null where that is applied: a type argument within the declared bound
 * of its type parameter, instantiated, is within the effective bound of a reference to it (adjust).
 *)
Lemma within_adjust: forall K D m (nn: bool) Z, tfrag env D = true -> bound_in env b K [] D = true ->
    in_fragment env Z = true -> Model.is_subtype_of (mutability_of env Z) m = true ->
    (exists f, unify env f (inst_nested env b D) Z (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (inst_nested env b (adjust env m nn D)) (if nn then without_null Z else Z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros K D m nn Z HD Hb HZ Hm [f H].
    (* intersections: each component takes what it took before *)
    assert (Hinter: forall cs W, components_sfrag env cs = true -> bound_in env b K [] (Intersection cs) = true ->
        in_fragment env W = true -> Model.is_subtype_of (mutability_of env W) m = true ->
        forall f0, unify env f0 (inst_nested env b (Intersection cs)) W (Ongoing []) = Some (Ongoing []) ->
        is_nullable W = false /\ exists ys f', inst_nested env b (Intersection (map (with_mutability env m) cs)) = Intersection ys
            /\ unify env f' (Intersection ys) W (Ongoing []) = Some (Ongoing [])).
    { clear f H. intros cs W Hcs Hbc HW HmW f0 E.
      destruct (components_sfrag_facts env cs Hcs) as [Hl Hc].
      assert (Hcomp: forall c, In c cs ->
          (exists md d args, c = RootResolved md d args)
          \/ (exists g o x, c = Generic g /\ lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o x)
              /\ in_fragment env x = true)).
      { intros c Hin. destruct (Hc c Hin) as [Hsh _].
        destruct c as [md d args| |g| | | |]; try (unfold is_component_shape in Hsh; simpl in Hsh; discriminate Hsh).
        - left. eauto.
        - right. destruct (binds_ref_some env b K [] g (bound_in_component env b K [] cs _ Hbc Hin)) as [o [x [Ex _]]].
          exists g, o, x. split; [reflexivity|]. split; [exact Ex|exact (Hbf _ o x Ex)]. }
      assert (Hn: forall c, In c cs -> is_nullable (inst_nested env b c) = false).
      { intros c Hin. destruct (Hc c Hin) as [Hsh Hsc].
        exact (proj2 (proj2 (instance_facts env wf b K [] Hbf (sdepth c) c (le_n _) (sfrag_tfrag env c Hsc)
            (bound_in_component env b K [] cs _ Hbc Hin))) (component_non_null c Hsh)). }
      destruct (intersection_instance env wf b K [] Hbf cs Hcs Hbc Hn) as [HeqY [Hcc Hfacts]].
      set (ys := map (inst_nested env b) cs) in *. set (cm := common_mutability env ys) in *.
      rewrite HeqY in E. destruct f0 as [|f1]; [discriminate E|].
      destruct (inter_accepts env wf f1 _ W [] [] Hcc HW E) as [_ [HnW Hall]].
      split; [exact HnW|].
      set (inst' := fun c => inst_nested env b (with_mutability env m c)).
      (* the components, of the mutability applied *)
      assert (Hc': forall c, In c cs -> is_class (inst' c) = true /\ in_fragment env (inst' c) = true
          /\ remut (inst_nested env b c) (inst' c)
          /\ forall k, Model.is_subtype_of k m = true -> Model.is_subtype_of k (mutability_of env (inst_nested env b c)) = true ->
              Model.is_subtype_of k (mutability_of env (inst' c)) = true).
      { intros c Hin. destruct (Hcomp c Hin) as [[md [d [args ->]]]|[g [o [x [-> [Ex Hx]]]]]].
        - pose proof (Hfacts _ Hin) as [HfY _].
          change (inst' (RootResolved md d args)) with (with_mutability env m (inst_nested env b (RootResolved md d args))).
          split; [reflexivity|]. split; [exact (in_fragment_with_mutability env m _ HfY)|].
          split; [exact (remut_with_mutability env m _ HfY)|].
          intros k Hkm Hky. destruct (with_mutability_cases env _ HfY) as [Hw|Hw]; rewrite Hw; assumption.
        - destruct g as [gm nng q bq].
          assert (Ex': lookup_binding b (param_of (mkGenericRef (Some m) nng q (with_mutability env m bq))) = Some (TypeArgument Model.invariant o x))
              by exact Ex.
          change (inst' (Generic (mkGenericRef gm nng q bq))) with (inst_nested env b (Generic (mkGenericRef (Some m) nng q (with_mutability env m bq)))).
          rewrite (inst_nested_generic env b _ _ o x Ex'). rewrite (inst_nested_generic env b (mkGenericRef gm nng q bq) _ o x Ex).
          pose proof (Hn _ Hin) as Hn0. rewrite (inst_nested_generic env b _ _ o x Ex) in Hn0.
          assert (Hn1: is_nullable (inst_ref env (mkGenericRef (Some m) nng q (with_mutability env m bq)) x) = false)
              by (rewrite nullable_inst_ref by exact Hx; rewrite nullable_inst_ref in Hn0 by exact Hx; exact Hn0).
          pose proof (inst_ref_in_fragment env (mkGenericRef (Some m) nng q (with_mutability env m bq)) x Hx) as Hf1.
          split; [destruct (fragment_cases env _ Hf1) as [[? [? [? E1]]]|[? [? [? [E1 _]]]]]; rewrite E1 in Hn1 |- *;
              [reflexivity|discriminate Hn1]|].
          split; [exact Hf1|]. split; [exact (remut_class_instances _ _ x Hx Hn0 Hn1)|].
          intros k Hkm Hky. rewrite (mutability_inst_ref env _ x Hx).
          apply (inst_fit_mutability (mkGenericRef (Some m) nng q (with_mutability env m bq)) x m Hx eq_refl k Hkm).
          rewrite (mutability_inst_ref env _ x Hx) in Hky. exact (mutability_subtype_trans _ _ _ Hky (inst_fit_mutability_below env _ x Hx)). }
      assert (Hys': forall y, In y (map inst' cs) -> is_class y = true /\ in_fragment env y = true).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. destruct (Hc' c Hin) as [H1 [H2 _]]. split; assumption. }
      assert (Hl': 2 <= length (map inst' cs)) by (rewrite length_map; exact Hl).
      destruct (of_classes env _ Hl' Hys') as [Heq' Hcc'].
      assert (Hmap: map (inst_component env b) (map (with_mutability env m) cs) = map inst' cs).
      { rewrite map_map. apply map_ext_in. intros c Hin. apply inst_component_nested.
        destruct (Hcomp c Hin) as [[md [d [args ->]]]|[[gm nng q bq] [o [x [-> _]]]]]; [reflexivity|].
        destruct (Hc _ Hin) as [Hsh _]. unfold is_component_shape in Hsh |- *. cbn [is_class is_generic orb with_mutability is_nullable] in Hsh |- *.
        rewrite (is_nullable_with_mutability env m bq). exact Hsh. }
      (* what W is below *)
      assert (HWy: forall c, In c cs -> Model.is_subtype_of (mutability_of env W) (mutability_of env (inst_nested env b c)) = true).
      { intros c Hin. destruct (Hfacts c Hin) as [HfY Hcm].
        assert (Hin': In (with_mutability env cm (inst_nested env b c)) (map (with_mutability env cm) ys))
            by (apply in_map; unfold ys; apply in_map, Hin).
        pose proof (accepted_mutability_classes env f1 _ W [] [] (in_fragment_with_mutability env cm _ HfY) HW (Hall _ Hin')) as Hm0.
        destruct (with_mutability_cases env _ HfY) as [Hw|Hw]; rewrite Hw in Hm0; [exact (mutability_subtype_trans _ _ _ Hm0 Hcm)|exact Hm0]. }
      exists (map (with_mutability env (common_mutability env (map inst' cs))) (map inst' cs)), (S f1).
      split; [change (inst_intersection env b (map (with_mutability env m) cs) = Intersection (map (with_mutability env (common_mutability env (map inst' cs))) (map inst' cs)));
          unfold inst_intersection; rewrite Hmap; exact Heq'|].
      apply (inter_takes env f1 _ W [] Hcc' HW HnW). intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']].
      apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]]. destruct (Hc' c Hin) as [_ [Hf' [Hr' Hk']]].
      destruct (Hfacts c Hin) as [HfY _].
      assert (Hin': In (with_mutability env cm (inst_nested env b c)) (map (with_mutability env cm) ys))
          by (apply in_map; unfold ys; apply in_map, Hin).
      apply (unify_remut env f1 (with_mutability env cm (inst_nested env b c)) _ W W [] []); [|apply (remut_refl env), HW| |exact (Hall _ Hin')].
      + exact (remut_trans _ _ _ (remut_sym _ _ (remut_with_mutability env cm _ HfY))
            (remut_trans _ _ _ Hr' (remut_with_mutability env _ _ Hf'))).
      + destruct (with_mutability_cases env _ Hf') as [Hw|Hw]; rewrite Hw; [|exact (Hk' _ HmW (HWy c Hin))].
        unfold common_mutability. apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros k Hk. apply in_map_iff in Hk. destruct Hk as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c' [<- Hin2]].
        exact (proj2 (proj2 (proj2 (Hc' c' Hin2))) _ HmW (HWy c' Hin2)). }
    destruct (tfrag_cases env D HD) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases env D Hs) as [[md [c [args [-> _]]]]|[->|[[md [c [args [-> Hs']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + (* a class type *)
        pose proof (instance_in_fragment env wf b K [] Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn (RootResolved md c args)))
            with (if nn then without_null (with_mutability env m (inst_nested env b (RootResolved md c args)))
                  else with_mutability env m (inst_nested env b (RootResolved md c args))) by (destruct nn; reflexivity).
        exact (lift_class f _ Z m nn HY HZ Hm H).
      + (* Nothing *)
        pose proof (instance_in_fragment env wf b K [] Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn bottom_type))
            with (if nn then without_null (with_mutability env m (inst_nested env b bottom_type))
                  else with_mutability env m (inst_nested env b bottom_type)) by (destruct nn; reflexivity).
        exact (lift_class f _ Z m nn HY HZ Hm H).
      + (* a nullable class type *)
        pose proof (instance_in_fragment env wf b K [] Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn (Nullable (RootResolved md c args))))
            with (if nn then without_null (with_mutability env m (inst_nested env b (Nullable (RootResolved md c args))))
                  else with_mutability env m (inst_nested env b (Nullable (RootResolved md c args)))) by (destruct nn; reflexivity).
        exact (lift_class f _ Z m nn HY HZ Hm H).
      + (* a reference to a type parameter *)
        destruct (binds_ref_some env b K [] g Hb) as [o [x [Ex _]]]. pose proof (Hbf _ o x Ex) as Hx.
        rewrite (inst_nested_generic env b g _ o x Ex) in H. destruct g as [gm nng q bq].
        set (g'' := if nn then mkGenericRef (Some m) (nng || is_nullable (with_mutability env m bq)) q (without_null (with_mutability env m bq))
            else mkGenericRef (Some m) nng q (with_mutability env m bq)).
        assert (E'': inst_nested env b (adjust env m nn (Generic (mkGenericRef gm nng q bq))) = inst_ref env g'' x).
        { unfold g''. destruct nn; cbn [adjust without_null with_mutability]; apply (inst_nested_generic env b _ Model.invariant o x); exact Ex. }
        rewrite E''. apply (ref_lift f (mkGenericRef gm nng q bq) g'' x m Z nn Hx HZ ltac:(unfold g''; destruct nn; reflexivity) Hm _ (or_introl eq_refl));
            [|exact H].
        left. split; [reflexivity|]. intros Hn. destruct nn; [right; reflexivity|left].
        rewrite nullable_inst_ref in Hn |- * by exact Hx. unfold g'' in Hn. cbn [is_narrowed] in Hn |- *. exact Hn.
      + (* a nullable reference to a type parameter *)
        destruct (binds_ref_some env b K [] g Hb) as [o [x [Ex _]]]. pose proof (Hbf _ o x Ex) as Hx.
        rewrite (inst_nested_nullable_generic env b g _ o x Ex) in H. destruct g as [gm nng q bq].
        set (g' := mkGenericRef (Some m) nng q (with_mutability env m bq)).
        destruct nn.
        * assert (E'': inst_nested env b (adjust env m true (Nullable (Generic (mkGenericRef gm nng q bq)))) = inst_ref env (narrow_ref g') x)
              by (apply (inst_nested_generic env b _ Model.invariant o x); exact Ex).
          rewrite E''. apply (ref_lift f (mkGenericRef gm nng q bq) (narrow_ref g') x m Z true Hx HZ eq_refl Hm _ (or_intror eq_refl)); [|exact H].
          left. split; [reflexivity|]. intros _. right. reflexivity.
        * assert (E'': inst_nested env b (adjust env m false (Nullable (Generic (mkGenericRef gm nng q bq)))) = rewrap_nullable (inst_ref env g' x))
              by (apply (inst_nested_nullable_generic env b _ Model.invariant o x); exact Ex).
          rewrite E''. exact (ref_lift f (mkGenericRef gm nng q bq) g' x m Z false Hx HZ eq_refl Hm _ (or_intror eq_refl) _ (or_intror eq_refl) H).
    - (* an intersection *)
      destruct (Hinter cs Z Hcs Hb HZ Hm f H) as [HnZ [ys [f' [Eys H']]]].
      replace (inst_nested env b (adjust env m nn (Intersection cs))) with (inst_nested env b (Intersection (map (with_mutability env m) cs)))
          by (destruct nn; reflexivity).
      rewrite Eys. exists f'. destruct nn; [rewrite (without_null_non_null env Z HZ HnZ)|]; exact H'.
    - (* a nullable intersection *)
      destruct f as [|f]; [discriminate H|].
      change (inst_nested env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection cs))) in H.
      destruct (intersection_instance env wf b K [] Hbf cs Hcs Hb) as [HeqY _].
      { intros c Hin. destruct (components_sfrag_facts env cs Hcs) as [_ Hc]. destruct (Hc c Hin) as [Hsh Hsc].
        exact (proj2 (proj2 (instance_facts env wf b K [] Hbf (sdepth c) c (le_n _) (sfrag_tfrag env c Hsc)
            (bound_in_component env b K [] cs _ Hb Hin))) (component_non_null c Hsh)). }
      rewrite HeqY in H. cbn [rewrap_nullable] in H. rewrite (unify_nullable_target env f _ Z [] HZ) in H. rewrite <- HeqY in H.
      pose proof (in_fragment_without_null env Z HZ) as HZ'.
      destruct (Hinter cs (without_null Z) Hcs Hb HZ' ltac:(rewrite (mutability_of_without_null env Z HZ); exact Hm) f H)
          as [_ [ys [f' [Eys H']]]].
      destruct nn.
      + replace (inst_nested env b (adjust env m true (Nullable (Intersection cs)))) with (inst_nested env b (Intersection (map (with_mutability env m) cs)))
            by reflexivity.
        rewrite Eys. exists f'. exact H'.
      + replace (inst_nested env b (adjust env m false (Nullable (Intersection cs))))
            with (rewrap_nullable (inst_nested env b (Intersection (map (with_mutability env m) cs)))) by reflexivity.
        rewrite Eys. exists (S f'). cbn [rewrap_nullable]. rewrite (unify_nullable_target env f' _ Z [] HZ). exact H'.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Every reference within its bound                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma respects_mono: forall K K' x B, K <= K' -> respects env K [] x B = true -> respects env K' [] x B = true.
Proof.
    intros K K' x B Hle H. unfold respects in *. destruct (unify env K B x (Ongoing [])) as [[w|]|] eqn:E; try discriminate H.
    rewrite (unify_fuel_monotone env K K' _ _ _ _ Hle E). reflexivity.
Qed.

Lemma bound_in_mono: forall K K' t, K <= K' -> bound_in env b K [] t = true -> bound_in env b K' [] t = true.
Proof.
    intros K K' t Hle. remember (esize t) as e eqn:He. revert t He. induction e as [e IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm nn p bd]|me msg|v o n|g|cs]; cbn [bound_in] in H |- *; try exact H.
    - apply forallb_forall. intros a Ha. rewrite forallb_forall in H.
      apply (IH (esize a)); [pose proof (esize_in args a Ha); simpl; lia|reflexivity|exact (H a Ha)].
    - apply (IH (esize n)); [simpl; lia|reflexivity|exact H].
    - apply andb_true_iff in H. destruct H as [Hr Hbd]. apply andb_true_iff.
      split; [|apply (IH (esize bd)); [simpl; lia|reflexivity|exact Hbd]].
      unfold binds_ref in Hr |- *. cbn [param_of effective_bound] in Hr |- *.
      destruct (lookup_binding b p) as [[| | | |[] o x| |]|]; try discriminate Hr.
      apply andb_true_iff in Hr. destruct Hr as [Hox Hr]. rewrite Hox. exact (respects_mono K K' _ _ Hle Hr).
    - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite Ho. apply (IH (esize n)); [simpl; lia|reflexivity|exact Hn].
    - apply forallb_forall. intros a Ha. rewrite forallb_forall in H.
      apply (IH (esize a)); [pose proof (esize_in cs a Ha); simpl; lia|reflexivity|exact (H a Ha)].
Qed.

Lemma bound_in_list: forall l, (forall a, In a l -> exists K, bound_in env b K [] a = true) ->
    exists K, forall a, In a l -> bound_in env b K [] a = true.
Proof.
    intros l H. induction l as [|a l IH]; [exists 0; intros _ []|].
    destruct (H a (or_introl eq_refl)) as [K1 H1]. destruct (IH (fun a' Ha' => H a' (or_intror Ha'))) as [K2 H2].
    exists (max K1 K2). intros a' [<-|Ha'].
    - apply (bound_in_mono K1); [lia|exact H1].
    - apply (bound_in_mono K2); [lia|exact (H2 a' Ha')].
Qed.

(* The depth of a type, nullability aside: applying a mutability or removing null keeps it *)
Fixpoint rdepth (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments => S (list_max (map rdepth arguments))
    | Nullable n => rdepth n
    | Generic (mkGenericRef _ _ _ bound) => S (rdepth bound)
    | TypeArgument _ _ n => S (rdepth n)
    | Intersection cs => S (list_max (map rdepth cs))
    | _ => 0
    end.

Lemma rdepth_below: forall l a, In a l -> rdepth a < S (list_max (map rdepth l)).
Proof.
    intros l a Ha. assert (H: Forall (fun k => k <= list_max (map rdepth l)) (map rdepth l)) by (apply list_max_le; lia).
    rewrite Forall_forall in H. specialize (H (rdepth a) (in_map _ _ _ Ha)). lia.
Qed.

Lemma rdepth_rewrap: forall t, rdepth (rewrap_nullable t) = rdepth t.
Proof. intros [| | | | | |]; reflexivity. Qed.

Lemma rdepth_with_mutability: forall m t, rdepth (with_mutability env m t) = rdepth t.
Proof.
    intros m t. remember (esize t) as e eqn:He. revert t He. induction e as [e IH] using lt_wf_ind. intros t ->.
    destruct t as [mt c args|n|[gm nn p bd]|me msg|v o n|[gm nn p bd]|cs]; try reflexivity.
    - cbn [with_mutability rdepth]. rewrite rdepth_rewrap. exact (IH (esize n) ltac:(simpl; lia) n eq_refl).
    - cbn [with_mutability rdepth]. rewrite (IH (esize bd) ltac:(simpl; lia) bd eq_refl). reflexivity.
    - cbn [with_mutability rdepth]. rewrite (IH (esize n) ltac:(simpl; lia) n eq_refl). reflexivity.
    - cbn [with_mutability rdepth]. rewrite map_map. do 2 f_equal. apply map_ext_in. intros c Hc.
      apply (IH (esize c)); [pose proof (esize_in cs c Hc); simpl; lia|reflexivity].
Qed.

Lemma rdepth_without_null: forall t, rdepth (without_null t) = rdepth t.
Proof.
    fix IH 1. intros [mt c args|n|[gm nn p bd]|me msg|v o n|g|cs]; cbn [without_null rdepth]; try reflexivity.
    - apply IH.
    - rewrite (IH bd). reflexivity.
    - rewrite (IH n). reflexivity.
Qed.

Lemma rdepth_adjust: forall m nn d, rdepth (adjust env m nn d) = rdepth d.
Proof. intros m [|] d; unfold adjust; rewrite ?rdepth_without_null; apply rdepth_with_mutability. Qed.

Section Derivation.

Variable declared: TypeParameterId -> EType.
(* The type parameters of the caller *)
Variable ps: list TypeParameterId.

Definition given_or_declared (gm: option Mutability) (p: TypeParameterId): Mutability :=
    match gm with Some m => m | None => mutability_of env (declared p) end.

(* The references to type parameters, as GenericTypeReference makes them: the effective bound is the
   declared bound, with the given mutability and the `!` applied (adjust); without a given mutability,
   with its own *)
Fixpoint built (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => built a /\ acc) True arguments
    | Nullable n => built n
    | Generic (mkGenericRef gm nn p bound) => bound = adjust env (given_or_declared gm p) nn (declared p) /\ built bound
    | TypeArgument _ _ n => built n
    | Intersection cs => fold_right (fun c acc => built c /\ acc) True cs
    | _ => True
    end.

(* The type parameters mentioned, in references and as ownership, are those of the caller *)
Fixpoint mentions_only (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => mentions_only a /\ acc) True arguments
    | Nullable n => mentions_only n
    | Generic (mkGenericRef _ _ p bound) => In p ps /\ mentions_only bound
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q ps) /\ mentions_only n
    | Intersection cs => fold_right (fun c acc => mentions_only c /\ acc) True cs
    | _ => True
    end.

(* A reference of a given mutability, to a type parameter bound to a core scalar, which stays
   immutable whatever the mutability given, is of a mutability core scalars have (see Substitution.v:
   `mut T` with T bound to a scalar takes nothing) *)
Fixpoint scalar_fits (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => scalar_fits a /\ acc) True arguments
    | Nullable n => scalar_fits n
    | Generic ((mkGenericRef gm _ p bound) as g) =>
        (forall m o x, gm = Some m -> lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
            Model.is_subtype_of (mutability_of env (inst_fit env g x)) m = true) /\ scalar_fits bound
    | TypeArgument _ _ n => scalar_fits n
    | Intersection cs => fold_right (fun c acc => scalar_fits c /\ acc) True cs
    | _ => True
    end.

(* The type parameters of the caller are bound exactly, each to a type within its declared bound,
   instantiated: as Kotlin checks type arguments *)
Hypothesis Hwithin: forall p, In p ps -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
    /\ is_exact_ownership o = true
    /\ exists f, unify env f (inst_nested env b (declared p)) x (Ongoing []) = Some (Ongoing []).
(* Their declared bounds are of tfrag, and the references in them as above *)
Hypothesis Hdeclared: forall p, In p ps ->
    tfrag env (declared p) = true /\ built (declared p) /\ mentions_only (declared p) /\ scalar_fits (declared p).

Definition derivable (t: EType): Prop :=
    built t -> mentions_only t -> scalar_fits t -> exists K, bound_in env b K [] t = true.

Lemma derive_step: forall k, (forall t, rdepth t < k -> derivable t) -> forall t, rdepth t <= k -> derivable t.
Proof.
    intros k IHk t. remember (esize t) as e eqn:He. revert t He. induction e as [e IHe] using lt_wf_ind. intros t -> Hd Hbt Hmo Hsf.
    assert (Hlist: forall l, (forall a, In a l -> esize a < esize t /\ rdepth a <= k /\ built a /\ mentions_only a /\ scalar_fits a) ->
        exists K, forallb (bound_in env b K []) l = true).
    { intros l Hl. destruct (bound_in_list l) as [K HK].
      - intros a Ha. destruct (Hl a Ha) as [Hs [Hda [Hb1 [Hm1 Hs1]]]]. exact (IHe (esize a) Hs a eq_refl Hda Hb1 Hm1 Hs1).
      - exists K. apply forallb_forall. exact HK. }
    destruct t as [m c args|n|[gm nn p bd]|me msg|v o n|g|cs].
    - destruct (Hlist args) as [K HK]; [|exists K; exact HK].
      intros a Ha. pose proof (esize_in args a Ha). pose proof (rdepth_below args a Ha). simpl in Hd |- *.
      split; [lia|]. split; [lia|]. split; [exact (fold_and_in _ args Hbt a Ha)|].
      split; [exact (fold_and_in _ args Hmo a Ha)|exact (fold_and_in _ args Hsf a Ha)].
    - exact (IHe (esize n) ltac:(simpl; lia) n eq_refl Hd Hbt Hmo Hsf).
    - (* a reference: within its bound, by the declared bound *)
      destruct Hbt as [Ebd Hbbd]. destruct Hmo as [Hp Hmbd]. destruct Hsf as [Hsg Hsbd].
      cbn [rdepth] in Hd.
      destruct (IHe (esize bd) ltac:(simpl; lia) bd eq_refl ltac:(lia) Hbbd Hmbd Hsbd) as [K1 HK1].
      destruct (Hdeclared p Hp) as [HtD [HbD [HmD HsD]]].
      assert (HdD: rdepth (declared p) < k) by (rewrite Ebd, rdepth_adjust in Hd; lia).
      destruct (IHk (declared p) HdD HbD HmD HsD) as [K2 HK2].
      destruct (Hwithin p Hp) as [o [x [Ex [Ho [f0 Hf0]]]]]. pose proof (Hbf _ o x Ex) as Hx.
      set (g := mkGenericRef gm nn p bd).
      destruct (instance_facts env wf b K2 [] Hbf (sdepth (declared p)) (declared p) (le_n _) HtD HK2) as [HcD [HmiD _]].
      pose proof (inst_fit_in_fragment env g x Hx) as HZ.
      assert (HmZ: Model.is_subtype_of (mutability_of env (inst_fit env g x)) (given_or_declared gm p) = true).
      { destruct gm as [m0|].
        - exact (Hsg m0 o x eq_refl Ex).
        - unfold inst_fit. cbn [given_mutability g]. cbn [given_or_declared].
          exact (mutability_subtype_trans _ _ _ (cfrag_mutability env wf f0 _ x [] [] HcD Hx Hf0) HmiD). }
      destruct (cfrag_lower f0 _ x _ HcD Hx HZ (remut_inst_fit env g x Hx) (inst_fit_mutability_below env g x Hx) Hf0) as [f1 Hf1].
      destruct (within_adjust K2 (declared p) (given_or_declared gm p) nn _ HtD HK2 HZ HmZ (ex_intro _ f1 Hf1)) as [f Hf].
      rewrite <- Ebd in Hf.
      exists (max K1 f).
      change (binds_ref env b (max K1 f) [] g && bound_in env b (max K1 f) [] bd = true).
      rewrite (bound_in_mono K1 (max K1 f) bd ltac:(lia) HK1), andb_true_r.
      unfold binds_ref. cbn [param_of effective_bound g]. rewrite Ex, Ho, (in_fragment_is_gfrag env x Hx). cbn [andb].
      unfold respects. replace (inst_ref env g x) with (if nn then without_null (inst_fit env g x) else inst_fit env g x)
          by (unfold inst_ref; reflexivity).
      rewrite (unify_fuel_monotone env f (max K1 f) _ _ _ _ ltac:(lia) Hf). reflexivity.
    - exists 0. reflexivity.
    - destruct Hmo as [Hq Hmn]. cbn [rdepth] in Hd.
      destruct (IHe (esize n) ltac:(simpl; lia) n eq_refl ltac:(lia) Hbt Hmn Hsf) as [K HK].
      exists K. change (ownership_bound b o && bound_in env b K [] n = true). rewrite HK, andb_true_r.
      destruct o as [| | |q]; try reflexivity.
      destruct (Hwithin q (Hq q eq_refl)) as [o' [x [Ex [Ho _]]]]. cbn [ownership_bound]. rewrite Ex. exact Ho.
    - exists 0. destruct g as [gm nn p bd]. reflexivity.
    - destruct (Hlist cs) as [K HK]; [|exists K; exact HK].
      intros a Ha. pose proof (esize_in cs a Ha). pose proof (rdepth_below cs a Ha). simpl in Hd |- *.
      split; [lia|]. split; [lia|]. split; [exact (fold_and_in _ cs Hbt a Ha)|].
      split; [exact (fold_and_in _ cs Hmo a Ha)|exact (fold_and_in _ cs Hsf a Ha)].
Qed.

(*
 * Every reference in a type, as GenericTypeReference makes them, to a type parameter of the caller,
 * is within its bound, instantiated (bound_in), where the type parameters are bound to types within
 * their declared bounds, instantiated
 *)
Theorem bound_in_derived: forall t, built t -> mentions_only t -> scalar_fits t -> exists K, bound_in env b K [] t = true.
Proof.
    intros t. remember (rdepth t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t Hk.
    apply (derive_step k); [|lia]. intros t' Ht'. exact (IH (rdepth t') ltac:(lia) t' eq_refl).
Qed.

End Derivation.

End Bindings.

End WithinBounds.

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
(* bound (GenericTypeReference.effectiveBound, Subtyping.effective_bound).                        *)
(* within_adjust shows a type below the declared bound, of no more than the mutability applied,   *)
(* below the bound with it applied, shape by shape of the declared bound: class types, references *)
(* to other type parameters, intersections, nullable or not.                                      *)
(*                                                                                                *)
(* That holds for a reference of a mutability const classes don't have (`mut T`) to a type        *)
(* parameter bound to one, too: its references are immutable, but its values are assigned as      *)
(* exclusive, below every mutability (inst_fit_below_given).                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Section WithinBounds.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

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

Lemma remut_without_null: forall t t', remut t t' -> remut (without_null env t) (without_null env t').
Proof.
    intros t t' [[m [m' [c [args [-> ->]]]]]|[m [m' [c [args [-> ->]]]]]]; left; exists m, m', c, args; split; reflexivity.
Qed.

(* Removing null from both sides of x and of a class type of x of another mutability *)
Lemma remut_derived: forall x t, in_fragment env x = true -> remut x t ->
    remut (without_null env x) (without_null env t).
Proof. intros x t _ H. exact (remut_without_null x t H). Qed.

Lemma remut_inst_ref: forall g x, in_fragment env x = true -> remut (without_null env x) (without_null env (inst_ref env g x)).
Proof.
    intros g x Hx. pose proof (remut_without_null _ _ (remut_inst_fit env g x Hx)) as H.
    unfold inst_ref. destruct (is_narrowed g); [|exact H].
    rewrite (without_null_idempotent env _ (inst_fit_in_fragment env g x Hx)). exact H.
Qed.

Lemma mutability_rewrap: forall t, in_fragment env t = true -> assignment_mutability env (rewrap_nullable t) = assignment_mutability env t.
Proof.
    intros t H. rewrite (rewrap_without_null env t H). change (assignment_mutability env (without_null env t) = assignment_mutability env t).
    exact (assignment_mutability_of_without_null env t H).
Qed.

Lemma nullable_rewrap: forall t, is_nullable env (rewrap_nullable t) = true.
Proof. intros [| | | | | |]; reflexivity. Qed.

(* x below a class type is below the same class type of another mutability that fits, and without
   null where that is *)
Lemma lift: forall n y t z (nn: bool), in_fragment env y = true -> in_fragment env t = true -> in_fragment env z = true ->
    remut (without_null env y) (without_null env t) ->
    Model.is_subtype_of (assignment_mutability env z) (assignment_mutability env t) = true ->
    (is_nullable env t = false -> is_nullable env y = false \/ nn = true) ->
    unify env n y z (Ongoing []) = Some (Ongoing []) ->
    exists n', unify env n' t (if nn then without_null env z else z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n y t z nn HY HT HZ Hr Hm Hn H.
    pose proof (unify_without_null env n y z [] [] HY HZ H) as H2.
    assert (H3: unify env n (without_null env t) (without_null env z) (Ongoing []) = Some (Ongoing [])).
    { apply (unify_remut env n (without_null env y) (without_null env t) (without_null env z) (without_null env z) [] [] Hr
          (remut_refl env _ (in_fragment_without_null env z HZ))); [|exact H2].
      rewrite (assignment_mutability_of_without_null env z HZ), (assignment_mutability_of_without_null env t HT). exact Hm. }
    destruct (is_nullable env t) eqn:EnT.
    - exists (S n). destruct (fragment_cases env t HT) as [[mt [ct [targs ->]]]|[mt [ct [targs [-> _]]]]]; [discriminate EnT|].
      assert (HZ': in_fragment env (if nn then without_null env z else z) = true)
          by (destruct nn; [apply in_fragment_without_null|]; exact HZ).
      rewrite (unify_nullable_target env n _ _ [] HZ').
      replace (without_null env (if nn then without_null env z else z)) with (without_null env z)
          by (destruct nn; [symmetry; apply (without_null_idempotent env z HZ)|reflexivity]).
      exact H3.
    - rewrite (without_null_non_null env t HT EnT) in H3. exists n. destruct nn; [exact H3|].
      destruct (Hn eq_refl) as [HnY|E]; [|discriminate E].
      rewrite (without_null_non_null env z HZ (accepted_non_null env n y z [] [] HY HZ HnY H)) in H3. exact H3.
Qed.

Section Bindings.

Variable b: Bindings.
Hypothesis Hbf: bindings_in_fragment env b.

(* A class type of x of a lower mutability is below what x is below *)
Lemma cfrag_lower: forall n y x z, cfrag env y = true -> in_fragment env x = true -> in_fragment env z = true ->
    remut x z -> Model.is_subtype_of (assignment_mutability env z) (assignment_mutability env x) = true ->
    unify env n y x (Ongoing []) = Some (Ongoing []) -> exists n', unify env n' y z (Ongoing []) = Some (Ongoing []).
Proof.
    intros n y x z HY Hx HZ Hr Hm H.
    assert (Hinter: forall f0 ys x z, class_components env ys = true -> in_fragment env x = true -> in_fragment env z = true ->
        remut x z -> Model.is_subtype_of (assignment_mutability env z) (assignment_mutability env x) = true ->
        unify env (S f0) (Intersection ys) x (Ongoing []) = Some (Ongoing []) ->
        unify env (S f0) (Intersection ys) z (Ongoing []) = Some (Ongoing [])).
    { clear x z Hx HZ Hr Hm H. intros f0 ys x z Hys Hx' HZ' Hr' Hm' E. destruct (inter_accepts env wf f0 ys x [] [] Hys Hx' E) as [_ [Hnx Hall]].
      destruct (class_components_facts env ys Hys) as [_ Hc].
      apply (inter_takes env f0 ys z [] Hys HZ').
      - destruct Hr' as [[m [m' [c [args [-> ->]]]]]|[m [m' [c [args [-> ->]]]]]]; [reflexivity|discriminate Hnx].
      - intros c Hin. apply (unify_remut env f0 c c x z [] [] (remut_refl env c (proj2 (Hc c Hin))) Hr'); [|exact (Hall c Hin)].
        exact (mutability_subtype_trans _ _ _ Hm' (accepted_mutability_classes env f0 c x [] [] (proj2 (Hc c Hin)) Hx' (Hall c Hin))). }
    destruct (cfrag_cases env y HY) as [HY'|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - exists n. apply (unify_remut env n y y x z [] [] (remut_refl env y HY') Hr); [|exact H].
      exact (mutability_subtype_trans _ _ _ Hm (accepted_mutability_classes env n y x [] [] HY' Hx H)).
    - destruct n as [|n]; [discriminate H|]. exists (S n). exact (Hinter n ys x z Hys Hx HZ Hr Hm H).
    - destruct n as [|n]; [discriminate H|]. exists (S n).
      rewrite (unify_nullable_target env n _ x [] Hx) in H. rewrite (unify_nullable_target env n _ z [] HZ).
      destruct n as [|n]; [discriminate H|].
      apply (Hinter n ys _ _ Hys (in_fragment_without_null env x Hx) (in_fragment_without_null env z HZ) (remut_without_null _ _ Hr));
          [|exact H].
      rewrite (assignment_mutability_of_without_null env z HZ), (assignment_mutability_of_without_null env x Hx). exact Hm.
Qed.

(* Below the instance of a reference, of a class type of x: below the instance of another reference
   to the same type parameter, of a mutability m that fits *)
Lemma ref_lift: forall n g1 g2 x m z (nn: bool), in_fragment env x = true -> in_fragment env z = true ->
    given_mutability g2 = Some m -> Model.is_subtype_of (assignment_mutability env z) m = true ->
    (forall y, y = inst_ref env g1 x \/ y = rewrap_nullable (inst_ref env g1 x) ->
        forall t, (t = inst_ref env g2 x /\ (is_nullable env t = false -> is_nullable env y = false \/ nn = true))
            \/ (t = rewrap_nullable (inst_ref env g2 x)) ->
        unify env n y z (Ongoing []) = Some (Ongoing []) ->
        exists n', unify env n' t (if nn then without_null env z else z) (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n g1 g2 x m z nn Hx HZ Hg Hm y HY t HT H.
    assert (HfY: in_fragment env y = true)
        by (destruct HY as [->| ->]; [|apply in_fragment_rewrap]; apply inst_ref_in_fragment, Hx).
    assert (HfT: in_fragment env t = true)
        by (destruct HT as [[-> _]| ->]; [|apply in_fragment_rewrap]; apply inst_ref_in_fragment, Hx).
    assert (HwY: without_null env y = without_null env (inst_ref env g1 x)) by (destruct HY as [->| ->]; [|apply without_null_rewrap]; reflexivity).
    assert (HwT: without_null env t = without_null env (inst_ref env g2 x))
        by (destruct HT as [[-> _]| ->]; [|apply without_null_rewrap]; reflexivity).
    assert (HmY: assignment_mutability env y = assignment_mutability env (inst_fit env g1 x)).
    { destruct HY as [->| ->]; [|rewrite (mutability_rewrap _ (inst_ref_in_fragment env g1 x Hx))]; apply mutability_inst_ref, Hx. }
    assert (HmT: assignment_mutability env t = assignment_mutability env (inst_fit env g2 x)).
    { destruct HT as [[-> _]| ->]; [|rewrite (mutability_rewrap _ (inst_ref_in_fragment env g2 x Hx))]; apply mutability_inst_ref, Hx. }
    apply (lift n y t z nn HfY HfT HZ).
    - rewrite HwY, HwT. exact (remut_trans _ _ _ (remut_sym _ _ (remut_inst_ref g1 x Hx)) (remut_inst_ref g2 x Hx)).
    - rewrite HmT. pose proof (accepted_mutability_classes env n y z [] [] HfY HZ H) as HZY. rewrite HmY in HZY.
      pose proof (mutability_subtype_trans _ _ _ HZY (inst_fit_mutability_below env g1 x Hx)) as HZx.
      unfold inst_fit. rewrite Hg.
      destruct (with_mutability_cases env x Hx) as [Hc|Hc]; rewrite Hc; [apply intersect_mutability_greatest|exact HZx].
      + exact (mutability_subtype_trans _ _ _ HZx (assignment_mutability_below env ranked x)).
      + exact Hm.
    - destruct HT as [[_ HT]| ->]; [exact HT|rewrite nullable_rewrap; discriminate].
    - exact H.
Qed.

(* Below a class type, below it of another mutability that fits, and without null *)
Lemma lift_class: forall n y z m (nn: bool), in_fragment env y = true -> in_fragment env z = true ->
    Model.is_subtype_of (assignment_mutability env z) m = true ->
    unify env n y z (Ongoing []) = Some (Ongoing []) ->
    exists n', unify env n' (if nn then without_null env (with_mutability env m y) else with_mutability env m y)
        (if nn then without_null env z else z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n y z m nn HY HZ Hm H. pose proof (in_fragment_with_mutability env m y HY) as HwY.
    apply (lift n y _ z nn HY); [destruct nn; [apply in_fragment_without_null|]; exact HwY|exact HZ| | | |exact H].
    - replace (without_null env (if nn then without_null env (with_mutability env m y) else with_mutability env m y))
          with (without_null env (with_mutability env m y)) by (destruct nn; [symmetry; apply (without_null_idempotent env _ HwY)|reflexivity]).
      exact (remut_without_null _ _ (remut_with_mutability env m y HY)).
    - replace (assignment_mutability env (if nn then without_null env (with_mutability env m y) else with_mutability env m y))
          with (assignment_mutability env (with_mutability env m y)) by (destruct nn; [symmetry; apply (assignment_mutability_of_without_null env _ HwY)|reflexivity]).
      pose proof (accepted_mutability_classes env n y z [] [] HY HZ H) as HZY.
      destruct (with_mutability_cases env y HY) as [Hc|Hc]; rewrite Hc; assumption.
    - intros Hn. destruct nn; [right; reflexivity|left]. rewrite (nullable_with_mutability env m y HY) in Hn. exact Hn.
Qed.

Lemma remut_class_instances: forall g g' x, in_fragment env x = true ->
    is_nullable env (inst_ref env g x) = false -> is_nullable env (inst_ref env g' x) = false ->
    remut (inst_ref env g x) (inst_ref env g' x).
Proof.
    intros g g' x Hx Hn Hn'.
    pose proof (remut_trans _ _ _ (remut_sym _ _ (remut_inst_ref g x Hx)) (remut_inst_ref g' x Hx)) as H.
    rewrite (without_null_non_null env _ (inst_ref_in_fragment env g x Hx) Hn),
        (without_null_non_null env _ (inst_ref_in_fragment env g' x Hx) Hn') in H.
    exact H.
Qed.

Lemma nullable_inst_ref: forall g x, in_fragment env x = true ->
    is_nullable env (inst_ref env g x) = negb (is_narrowed g) && is_nullable env x.
Proof.
    intros g x Hx. unfold inst_ref. destruct (is_narrowed g).
    - cbn [negb andb]. apply (Substitution.without_null_not_nullable env), (inst_fit_in_fragment env), Hx.
    - cbn [negb andb]. apply (nullable_inst_fit env), Hx.
Qed.

(* Of the mutability given, the instance of a reference is assigned as no more than it: the type
   argument of that mutability, or an object of a const class, exclusive *)
Lemma inst_fit_below_given: forall g x m, in_fragment env x = true -> given_mutability g = Some m ->
    Model.is_subtype_of (assignment_mutability env (inst_fit env g x)) m = true.
Proof.
    intros g x m Hx Hg. unfold inst_fit. rewrite Hg.
    destruct (fragment_cases env x Hx) as [[mx [c [args ->]]]|[mx [c [args [-> _]]]]]; simpl;
        destruct (is_const (declaration_of env c)); first [reflexivity|apply intersect_mutability_right].
Qed.

Lemma inst_fit_mutability: forall g x m0, in_fragment env x = true -> given_mutability g = Some m0 ->
    forall m1, Model.is_subtype_of m1 m0 = true -> Model.is_subtype_of m1 (assignment_mutability env x) = true ->
    Model.is_subtype_of m1 (assignment_mutability env (inst_fit env g x)) = true.
Proof.
    intros g x m0 Hx Hg m1 Hkm Hkx. unfold inst_fit. rewrite Hg.
    destruct (with_mutability_cases env x Hx) as [Hc|Hc]; rewrite Hc; [apply intersect_mutability_greatest|exact Hkx].
    - exact (mutability_subtype_trans _ _ _ Hkx (assignment_mutability_below env ranked x)).
    - exact Hkm.
Qed.

(*
 * What is below a type, instantiated, is below it with another mutability, of no more than what is
 * below, applied, and without null where that is applied: a type argument within the declared bound
 * of its type parameter, instantiated, is within the effective bound of a reference to it (adjust).
 *)
Lemma within_adjust: forall d0 t m (nn: bool) z, tfrag env t = true -> bex env b t = true -> bound_in_top_h env b d0 [] (top_bound_in env b d0 []) t = true ->
    in_fragment env z = true -> Model.is_subtype_of (assignment_mutability env z) m = true ->
    (exists n, unify env n (inst_nested env b t) z (Ongoing []) = Some (Ongoing [])) ->
    exists n, unify env n (inst_nested env b (adjust env m nn t)) (if nn then without_null env z else z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros d0 t m nn z HD Hb Htop HZ Hm [n H].
    (* intersections: each component takes what it took before *)
    assert (Hinter: forall m cs W, components_sfrag env cs = true -> bex env b (Intersection cs) = true -> bound_in_top_h env b d0 [] (top_bound_in env b d0 []) (Intersection cs) = true ->
        in_fragment env W = true -> Model.is_subtype_of (assignment_mutability env W) m = true ->
        forall f0, unify env f0 (inst_nested env b (Intersection cs)) W (Ongoing []) = Some (Ongoing []) ->
        is_nullable env W = false /\ exists ys f', inst_nested env b (Intersection (map (with_mutability env m) cs)) = Intersection ys
            /\ unify env f' (Intersection ys) W (Ongoing []) = Some (Ongoing [])).
    { clear n H Hm m. intros m cs W Hcs Hbc Htc HW HmW f0 E.
      destruct (components_sfrag_facts env cs Hcs) as [Hl Hc].
      assert (Hcomp: forall c, In c cs ->
          (exists md d args, c = RootResolved md d args)
          \/ (exists g o x, c = Generic g /\ lookup_binding b (param_of g) = Some (TypeArgument Model.invariant o x)
              /\ in_fragment env x = true)).
      { intros c Hin. destruct (Hc c Hin) as [Hsh _].
        destruct c as [md d args| |g| | | |]; try (unfold is_component_shape in Hsh; simpl in Hsh; discriminate Hsh).
        - left. eauto.
        - right. destruct (bex_some env b g (bex_component env b cs _ Hbc Hin)) as [o [x [Ex _]]].
          exists g, o, x. split; [reflexivity|]. split; [exact Ex|exact (Hbf _ o x Ex)]. }
      assert (Hn: forall c, In c cs -> is_nullable env (inst_nested env b c) = false).
      { intros c Hin. destruct (Hc c Hin) as [Hsh Hsc].
        exact (proj2 (proj2 (instance_facts_ex env wf b d0 [] Hbf _ c (le_n _) (sfrag_tfrag env c Hsc)
            (bex_component env b cs _ Hbc Hin) (top_component env b d0 [] cs _ Htc Hin))) (component_non_null env c Hsh)). }
      destruct (intersection_instance_ex env wf b Hbf cs Hcs Hbc Hn) as [HeqY [Hcc Hfacts]].
      set (ys := map (inst_nested env b) cs) in *. set (cm := common_mutability env ys) in *.
      rewrite HeqY in E. destruct f0 as [|f1]; [discriminate E|].
      destruct (inter_accepts env wf f1 _ W [] [] Hcc HW E) as [_ [HnW Hall]].
      split; [exact HnW|].
      set (inst' := fun c => inst_nested env b (with_mutability env m c)).
      (* the components, of the mutability applied *)
      assert (Hc': forall c, In c cs -> is_class (inst' c) = true /\ in_fragment env (inst' c) = true
          /\ remut (inst_nested env b c) (inst' c)
          /\ forall k, Model.is_subtype_of k m = true -> Model.is_subtype_of k (assignment_mutability env (inst_nested env b c)) = true ->
              Model.is_subtype_of k (assignment_mutability env (inst' c)) = true).
      { intros c Hin. destruct (Hcomp c Hin) as [[md [d [args ->]]]|[g [o [x [-> [Ex Hx]]]]]].
        - pose proof (Hfacts _ Hin) as [HfY _].
          change (inst' (RootResolved md d args)) with (with_mutability env m (inst_nested env b (RootResolved md d args))).
          split; [reflexivity|]. split; [exact (in_fragment_with_mutability env m _ HfY)|].
          split; [exact (remut_with_mutability env m _ HfY)|].
          intros k Hkm Hky. destruct (with_mutability_cases env _ HfY) as [Hw|Hw]; rewrite Hw; assumption.
        - destruct g as [gm nng q bq].
          assert (Ex': lookup_binding b (param_of (mkGenericRef (Some m) nng q bq)) = Some (TypeArgument Model.invariant o x))
              by exact Ex.
          change (inst' (Generic (mkGenericRef gm nng q bq))) with (inst_nested env b (Generic (mkGenericRef (Some m) nng q bq))).
          rewrite (inst_nested_generic env b _ _ o x Ex'). rewrite (inst_nested_generic env b (mkGenericRef gm nng q bq) _ o x Ex).
          pose proof (Hn _ Hin) as Hn0. rewrite (inst_nested_generic env b _ _ o x Ex) in Hn0.
          assert (Hn1: is_nullable env (inst_ref env (mkGenericRef (Some m) nng q bq) x) = false)
              by (rewrite nullable_inst_ref by exact Hx; rewrite nullable_inst_ref in Hn0 by exact Hx; exact Hn0).
          pose proof (inst_ref_in_fragment env (mkGenericRef (Some m) nng q bq) x Hx) as Hf1.
          split; [destruct (fragment_cases env _ Hf1) as [[? [? [? E1]]]|[? [? [? [E1 _]]]]]; rewrite E1 in Hn1 |- *;
              [reflexivity|discriminate Hn1]|].
          split; [exact Hf1|]. split; [exact (remut_class_instances _ _ x Hx Hn0 Hn1)|].
          intros k Hkm Hky. rewrite (mutability_inst_ref env _ x Hx).
          apply (inst_fit_mutability (mkGenericRef (Some m) nng q bq) x m Hx eq_refl k Hkm).
          rewrite (mutability_inst_ref env _ x Hx) in Hky. exact (mutability_subtype_trans _ _ _ Hky (inst_fit_mutability_below env _ x Hx)). }
      assert (Hys': forall y, In y (map inst' cs) -> is_class y = true /\ in_fragment env y = true).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]]. destruct (Hc' c Hin) as [H1 [H2 _]]. split; assumption. }
      assert (Hl': 2 <= length (map inst' cs)) by (rewrite length_map; exact Hl).
      destruct (of_classes env _ Hl' Hys') as [Heq' Hcc'].
      assert (Hmap: map (inst_component env b) (map (with_mutability env m) cs) = map inst' cs).
      { rewrite map_map. apply map_ext_in. intros c Hin. apply inst_component_nested.
        destruct (Hcomp c Hin) as [[md [d [args ->]]]|[[gm nng q bq] [o [x [-> _]]]]]; [reflexivity|].
        destruct (Hc _ Hin) as [Hsh _]. unfold is_component_shape in Hsh |- *.
        rewrite (is_nullable_with_mutability env wf m (Generic (mkGenericRef gm nng q bq))). exact Hsh. }
      (* what W is below *)
      assert (HWy: forall c, In c cs -> Model.is_subtype_of (assignment_mutability env W) (assignment_mutability env (inst_nested env b c)) = true).
      { intros c Hin. destruct (Hfacts c Hin) as [HfY Hcm].
        assert (Hin': In (with_mutability env cm (inst_nested env b c)) (map (with_mutability env cm) ys))
            by (apply in_map; unfold ys; apply in_map, Hin).
        pose proof (accepted_mutability_classes env f1 _ W [] [] (in_fragment_with_mutability env cm _ HfY) HW (Hall _ Hin')) as Hm0.
        pose proof (with_common_mutability env ys _ (in_map _ _ _ Hin) HfY) as Hcw. fold cm in Hcw. rewrite Hcw in Hm0.
        exact (mutability_subtype_trans _ _ _ Hm0 (fold_intersect_below_element _ _ _ (in_map _ _ _ (in_map _ _ _ Hin)))). }
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
      + rewrite (with_common_mutability env _ _ (in_map _ _ _ Hin) Hf').
        unfold common_mutability. apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros k Hk. apply in_map_iff in Hk. destruct Hk as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c' [<- Hin2]].
        exact (proj2 (proj2 (proj2 (Hc' c' Hin2))) _ HmW (HWy c' Hin2)). }
    (* what an intersection takes is assigned as no more than the mutability its components take *)
    assert (Hcommon: forall cs W f0, components_sfrag env cs = true -> bex env b (Intersection cs) = true -> bound_in_top_h env b d0 [] (top_bound_in env b d0 []) (Intersection cs) = true ->
        in_fragment env W = true -> Model.is_subtype_of (assignment_mutability env W) m = true ->
        unify env f0 (inst_nested env b (Intersection cs)) W (Ongoing []) = Some (Ongoing []) ->
        Model.is_subtype_of (assignment_mutability env W)
            (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly) = true).
    { intros cs W f0 Hcs Hbc Htc HW HmW E.
      destruct (instance_facts_ex env wf b d0 [] Hbf _ (Intersection cs) (le_n _) Hcs Hbc Htc) as [Hcf [Hmi _]].
      pose proof (mutability_subtype_trans _ _ _ (cfrag_mutability env wf _ _ W _ _ Hcf HW E) Hmi) as HWc.
      apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|]. intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hin]].
      eapply mutability_subtype_trans; [|apply (assignment_with_mutability_above env wf)].
      apply intersect_mutability_greatest; [exact HmW|].
      exact (mutability_subtype_trans _ _ _ HWc (fold_intersect_below_element _ _ _ (in_map _ _ _ Hin))). }
    destruct (tfrag_cases env t HD) as [Hs|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - destruct (sfrag_cases env wf t Hs) as [[md [c [args [-> _]]]]|[[m_bot ->]|[[md [c [args [-> Hs']]]]|[[g [-> Hg]]|[g [-> Hg]]]]]].
      + (* a class type *)
        pose proof (instance_in_fragment_ex env wf b Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn (RootResolved md c args)))
            with (if nn then without_null env (with_mutability env m (inst_nested env b (RootResolved md c args)))
                  else with_mutability env m (inst_nested env b (RootResolved md c args))) by (destruct nn; reflexivity).
        exact (lift_class n _ z m nn HY HZ Hm H).
      + (* Nothing *)
        pose proof (instance_in_fragment_ex env wf b Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn (RootResolved m_bot nothing [])))
            with (if nn then without_null env (with_mutability env m (inst_nested env b (RootResolved m_bot nothing [])))
                  else with_mutability env m (inst_nested env b (RootResolved m_bot nothing []))) by (destruct nn; reflexivity).
        exact (lift_class n _ z m nn HY HZ Hm H).
      + (* a nullable class type *)
        pose proof (instance_in_fragment_ex env wf b Hbf _ Hs Hb) as HY.
        replace (inst_nested env b (adjust env m nn (Nullable (RootResolved md c args))))
            with (if nn then without_null env (with_mutability env m (inst_nested env b (Nullable (RootResolved md c args))))
                  else with_mutability env m (inst_nested env b (Nullable (RootResolved md c args)))) by (destruct nn; reflexivity).
        exact (lift_class n _ z m nn HY HZ Hm H).
      + (* a reference to a type parameter *)
        destruct (bex_some env b g Hb) as [o [x [Ex _]]]. pose proof (Hbf _ o x Ex) as Hx.
        rewrite (inst_nested_generic env b g _ o x Ex) in H. destruct g as [gm nng q bq].
        set (g'' := if nn then mkGenericRef (Some m) (nng || is_nullable env (Generic (mkGenericRef (Some m) nng q bq))) q bq
            else mkGenericRef (Some m) nng q bq).
        assert (E'': inst_nested env b (adjust env m nn (Generic (mkGenericRef gm nng q bq))) = inst_ref env g'' x).
        { unfold g''. destruct nn; cbn [adjust without_null with_mutability]; apply (inst_nested_generic env b _ Model.invariant o x); exact Ex. }
        rewrite E''. apply (ref_lift n (mkGenericRef gm nng q bq) g'' x m z nn Hx HZ ltac:(unfold g''; destruct nn; reflexivity) Hm _ (or_introl eq_refl));
            [|exact H].
        left. split; [reflexivity|]. intros Hn. destruct nn; [right; reflexivity|left].
        rewrite nullable_inst_ref in Hn |- * by exact Hx. unfold g'' in Hn. cbn [is_narrowed] in Hn |- *. exact Hn.
      + (* a nullable reference to a type parameter *)
        destruct (bex_some env b g Hb) as [o [x [Ex _]]]. pose proof (Hbf _ o x Ex) as Hx.
        rewrite (inst_nested_nullable_generic env b g _ o x Ex) in H. destruct g as [gm nng q bq].
        set (g' := mkGenericRef (Some m) nng q bq).
        destruct nn.
        * assert (E'': inst_nested env b (adjust env m true (Nullable (Generic (mkGenericRef gm nng q bq)))) = inst_ref env (narrow_ref env g') x)
              by (apply (inst_nested_generic env b _ Model.invariant o x); exact Ex).
          rewrite E''. apply (ref_lift n (mkGenericRef gm nng q bq) (narrow_ref env g') x m z true Hx HZ eq_refl Hm _ (or_intror eq_refl)); [|exact H].
          left. split; [reflexivity|]. intros _. right. reflexivity.
        * assert (E'': inst_nested env b (adjust env m false (Nullable (Generic (mkGenericRef gm nng q bq)))) = rewrap_nullable (inst_ref env g' x))
              by (apply (inst_nested_nullable_generic env b _ Model.invariant o x); exact Ex).
          rewrite E''. exact (ref_lift n (mkGenericRef gm nng q bq) g' x m z false Hx HZ eq_refl Hm _ (or_intror eq_refl) _ (or_intror eq_refl) H).
    - (* an intersection *)
      destruct (Hinter _ cs z Hcs Hb Htop HZ (Hcommon cs z n Hcs Hb Htop HZ Hm H) n H) as [HnZ [ys [f' [Eys H']]]].
      replace (inst_nested env b (adjust env m nn (Intersection cs)))
          with (inst_nested env b (Intersection (map (with_mutability env (fold_left intersect_mutability
              (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly)) cs)))
          by (destruct nn; [|reflexivity]; unfold adjust;
              assert (Hwn: is_nullable env (with_mutability env m (Intersection cs)) = false)
                  by (rewrite (proj1 (proj2 (with_mutability_keeps env ranked m _))); exact (components_sfrag_not_nullable env cs HD));
              cbn [with_mutability] in Hwn |- *; rewrite (without_null_not_nullable_intersection env _ Hwn); reflexivity).
      rewrite Eys. exists f'. destruct nn; [rewrite (without_null_non_null env z HZ HnZ)|]; exact H'.
    - (* a nullable intersection *)
      destruct n as [|n]; [discriminate H|].
      change (inst_nested env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection cs))) in H.
      destruct (intersection_instance_ex env wf b Hbf cs Hcs Hb) as [HeqY _].
      { intros c Hin. destruct (components_sfrag_facts env cs Hcs) as [_ Hc]. destruct (Hc c Hin) as [Hsh Hsc].
        exact (proj2 (proj2 (instance_facts_ex env wf b d0 [] Hbf _ c (le_n _) (sfrag_tfrag env c Hsc)
            (bex_component env b cs _ Hb Hin) (top_component env b d0 [] cs _ Htop Hin))) (component_non_null env c Hsh)). }
      rewrite HeqY in H. cbn [rewrap_nullable] in H. rewrite (unify_nullable_target env n _ z [] HZ) in H. rewrite <- HeqY in H.
      pose proof (in_fragment_without_null env z HZ) as HZ'.
      assert (HmZ': Model.is_subtype_of (assignment_mutability env (without_null env z)) m = true)
          by (rewrite (assignment_mutability_of_without_null env z HZ); exact Hm).
      destruct (Hinter _ cs (without_null env z) Hcs Hb Htop HZ' (Hcommon cs _ n Hcs Hb Htop HZ' HmZ' H) n H) as [_ [ys [f' [Eys H']]]].
      set (k := fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly) in Eys.
      destruct nn.
      + replace (inst_nested env b (adjust env m true (Nullable (Intersection cs)))) with (inst_nested env b (Intersection (map (with_mutability env k) cs)))
            by (unfold adjust; assert (Hwn: is_nullable env (with_mutability env m (Intersection cs)) = false)
                    by (rewrite (proj1 (proj2 (with_mutability_keeps env ranked m _))); exact (components_sfrag_not_nullable env cs Hcs));
                cbn [with_mutability rewrap_nullable without_null is_nullable] in Hwn |- *; rewrite Hwn; reflexivity).
        rewrite Eys. exists f'. exact H'.
      + replace (inst_nested env b (adjust env m false (Nullable (Intersection cs))))
            with (rewrap_nullable (inst_nested env b (Intersection (map (with_mutability env k) cs)))) by reflexivity.
        rewrite Eys. exists (S f'). cbn [rewrap_nullable]. rewrite (unify_nullable_target env f' _ z [] HZ). exact H'.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Every reference within its bound                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma respects_mono: forall d d' x B, d <= d' -> respects env d [] x B = true -> respects env d' [] x B = true.
Proof.
    intros d d' x B Hle H. unfold respects in *. destruct (unify env d B x (Ongoing [])) as [[w|]|] eqn:E; try discriminate H.
    rewrite (unify_fuel_monotone env d d' _ _ _ _ Hle E). reflexivity.
Qed.

Lemma bound_in_mono: forall d d' t, d <= d' -> bound_in env b d [] t = true -> bound_in env b d' [] t = true.
Proof.
    intros d d' t Hle. apply (bound_in_lift_any env wf b d [] b d' []); [|intros o Ho; exact Ho].
    intros g Hb. unfold binds_ref in Hb |- *.
    destruct (lookup_binding b (param_of g)) as [[| | | |[] o x| |]|]; try discriminate Hb.
    apply andb_true_iff in Hb. destruct Hb as [Hox Hb]. rewrite Hox. exact (respects_mono d d' _ _ Hle Hb).
Qed.

Lemma bound_in_list: forall xs, (forall a, In a xs -> exists d, bound_in env b d [] a = true) ->
    exists d, forall a, In a xs -> bound_in env b d [] a = true.
Proof.
    intros xs H. induction xs as [|a xs IH]; [exists 0; intros _ []|].
    destruct (H a (or_introl eq_refl)) as [K1 H1]. destruct (IH (fun a' Ha' => H a' (or_intror Ha'))) as [K2 H2].
    exists (max K1 K2). intros a' [<-|Ha'].
    - apply (bound_in_mono K1); [lia|exact H1].
    - apply (bound_in_mono K2); [lia|exact (H2 a' Ha')].
Qed.

Section Derivation.

Variable declared: TypeParameterId -> EType.
(* The type parameters of the caller *)
Variable ps: list TypeParameterId.

(* The references to type parameters, as GenericTypeReference makes them: the effective bound is the
   declared bound, with the given mutability and the `!` applied. That is how effective_bound makes it,
   so every type is built so. TODO: remove *)
Definition built (t: EType): Prop := let _ := (env, declared) in True.

(* The type parameters mentioned, in references and as ownership, are those of the caller, also in
   the declared bounds of the parameters of references (see Subtyping.through_param), which
   mentions_only_h takes from bound_mentions_only; references without type variables *)
Fixpoint mentions_only_h (bound_mentions_only: TypeParameterId -> Prop) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => mentions_only_h bound_mentions_only a /\ acc) True arguments
    | Nullable n => mentions_only_h bound_mentions_only n
    | Generic g => In (param_of g) ps /\ variables_of g = [] /\ bound_mentions_only (param_of g)
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q ps) /\ mentions_only_h bound_mentions_only n
    | Intersection cs => fold_right (fun c acc => mentions_only_h bound_mentions_only c /\ acc) True cs
    | _ => True
    end.

Definition param_mentions_only (p: TypeParameterId): Prop := through_param env mentions_only_h True p.

Fixpoint mentions_only (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => mentions_only a /\ acc) True arguments
    | Nullable n => mentions_only n
    | Generic g => In (param_of g) ps /\ variables_of g = [] /\ param_mentions_only (param_of g)
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q ps) /\ mentions_only n
    | Intersection cs => fold_right (fun c acc => mentions_only c /\ acc) True cs
    | _ => True
    end.

Let deep := wf_bounds_deep_ranked env wf.

Lemma mentions_only_top: forall t, mentions_only t = mentions_only_h param_mentions_only t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity; try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma mentions_only_h_agree: forall p k Q1 Q2, (forall q, q = p \/ parameter_rank env q < k -> Q1 q = Q2 q) ->
    forall t, deep_ranked env p k t = true -> mentions_only_h Q1 t = mentions_only_h Q2 t.
Proof.
    intros p k Q1 Q2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity; try exact (IH n Ht).
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - rewrite (HU _ (deep_ranked_param env p k g Ht)). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma mentions_only_h_mono: forall Q1 Q2, (forall q, Q1 q -> Q2 q) -> forall t, mentions_only_h Q1 t -> mentions_only_h Q2 t.
Proof.
    intros Q1 Q2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try exact Ht; try exact (IH n Ht).
    - induction args as [|a args IHa]; [exact I|]. destruct Ht as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - destruct Ht as [Hp [Hv Hu]]. exact (conj Hp (conj Hv (HU _ Hu))).
    - destruct Ht as [Ho Hn]. exact (conj Ho (IH n Hn)).
    - induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

Lemma param_mentions_only_iff: forall p, param_mentions_only p <-> mentions_only (parameter_bound env p).
Proof.
    intros p. rewrite mentions_only_top. unfold param_mentions_only at 1.
    exact (through_param_fix_prop env mentions_only_h deep mentions_only_h_agree (fun U1 U2 t H => mentions_only_h_mono U1 U2 H t) p).
Qed.

(* A mutability applied, or null removed, mentions the same *)
Lemma mentions_only_adjust: forall t,
    (forall m, mentions_only (with_mutability env m t) <-> mentions_only t) /\ (mentions_only (without_null env t) <-> mentions_only t).
Proof.
    fix IH 1. intros [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; split; try intros m; try reflexivity.
    - cbn [with_mutability]. change (mentions_only (Nullable n)) with (mentions_only n). rewrite <- (proj1 (IH n) m).
      destruct (with_mutability env m n); reflexivity.
    - exact (proj2 (IH n)).
    - simpl. rewrite (proj1 (IH n) m). reflexivity.
    - simpl. rewrite (proj2 (IH n)). reflexivity.
    - simpl. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly).
      intros k. clear m. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj1 (IH c) k), IHc. reflexivity.
    - cbn [without_null]. destruct (forallb _ cs); [|reflexivity]. simpl.
      induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj2 (IH c)), IHc. reflexivity.
Qed.

Lemma mentions_only_with_mutability: forall m t, mentions_only t -> mentions_only (with_mutability env m t).
Proof. intros m t H. apply (proj1 (mentions_only_adjust t) m), H. Qed.

Lemma mentions_only_without_null: forall t, mentions_only t -> mentions_only (without_null env t).
Proof. intros t H. apply (proj2 (mentions_only_adjust t)), H. Qed.

(* The effective bound of a reference mentions only the type parameters of the caller where the
   declared bound of its parameter does *)
Lemma mentions_only_bound: forall gm nn p, mentions_only (parameter_bound env p) ->
    mentions_only (effective_bound env (mkGenericRef gm nn p [])).
Proof.
    intros gm nn p H. rewrite (effective_bound_eq env ranked). cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
    destruct gm as [m|], nn; cbn iota;
        try apply mentions_only_without_null; try apply mentions_only_with_mutability; exact H.
Qed.

Lemma mentions_only_generic: forall g, mentions_only (Generic g) -> mentions_only (effective_bound env g).
Proof.
    intros [gm nn p vs] [_ [Hv Hm]]. cbn [variables_of param_of] in Hv, Hm. subst vs.
    apply mentions_only_bound, param_mentions_only_iff, Hm.
Qed.

(* The type parameters of the caller are bound exactly, each to a type within its declared bound,
   instantiated: as Kotlin checks type arguments *)
Hypothesis Hwithin: forall p, In p ps -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
    /\ is_exact_ownership o = true
    /\ exists n, unify env n (inst_nested env b (declared p)) x (Ongoing []) = Some (Ongoing []).
(* Their declared bounds are of tfrag, and the references in them as above *)
Hypothesis Hdeclared: forall p, In p ps ->
    tfrag env (declared p) = true /\ built (declared p) /\ mentions_only (declared p).
(* They are the bounds of the type parameters *)
Hypothesis Hbound: forall p, declared p = parameter_bound env p.

(* The references in a type, those in its type arguments too, are of R, and the type parameters in
   the ownerships are bound exactly *)
Fixpoint refs_in (R: GenericRef -> Prop) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => refs_in R a /\ acc) True arguments
    | Nullable n => refs_in R n
    | Generic g => R g
    | TypeArgument _ o n => ownership_bound b o = true /\ refs_in R n
    | Intersection cs => fold_right (fun c acc => refs_in R c /\ acc) True cs
    | _ => True
    end.

Lemma refs_in_mono: forall (R1 R2: GenericRef -> Prop), (forall g0, R1 g0 -> R2 g0) -> forall t, refs_in R1 t -> refs_in R2 t.
Proof.
    intros R1 R2 HR. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try exact Ht; try exact (IH n Ht).
    - induction args as [|a args IHa]; [exact I|]. destruct Ht as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (HR g Ht).
    - destruct Ht as [Ho Hn]. exact (conj Ho (IH n Hn)).
    - induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

(* A mutability applied, or null removed, the references are of R where R doesn't tell them apart *)
Lemma refs_in_adjust: forall (R: GenericRef -> Prop), (forall gm nn gm' nn' p vs, R (mkGenericRef gm nn p vs) -> R (mkGenericRef gm' nn' p vs)) ->
    forall t, refs_in R t -> (forall m, refs_in R (with_mutability env m t)) /\ refs_in R (without_null env t).
Proof.
    intros R HR. fix IH 1. intros [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; split; try intros m; try exact Ht.
    - cbn [with_mutability]. destruct (IH n Ht) as [Hm _]. specialize (Hm m). destruct (with_mutability env m n); exact Hm.
    - exact (proj2 (IH n Ht)).
    - exact (HR _ _ _ _ _ _ Ht).
    - exact (HR _ _ _ _ _ _ Ht).
    - destruct Ht as [Ho Hn]. exact (conj Ho (proj1 (IH n Hn) m)).
    - destruct Ht as [Ho Hn]. exact (conj Ho (proj2 (IH n Hn))).
    - simpl. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly).
      intros k. clear m. induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (proj1 (IH c Hc) k) (IHc Hcs)).
    - cbn [without_null]. destruct (forallb (is_nullable env) cs); [|exact Ht]. simpl.
      induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (proj2 (IH c Hc)) (IHc Hcs)).
Qed.

Lemma ownership_bound_caller: forall o, (forall q, o = parameter_ownership q -> In q ps) -> ownership_bound b o = true.
Proof.
    intros [| | |q] H; try reflexivity. destruct (Hwithin q (H q eq_refl)) as [o [x [Ex [Ho _]]]].
    cbn [ownership_bound]. rewrite Ex. exact Ho.
Qed.

(* Of a type mentioning only the type parameters of the caller, the references are of R where R takes
   those to the parameters of a rank below k, and to p0 *)
Lemma refs_in_from_mentions: forall (R: GenericRef -> Prop) p0 k,
    (forall g0, In (param_of g0) ps -> variables_of g0 = [] -> parameter_rank env (param_of g0) < k \/ param_of g0 = p0 -> R g0) ->
    forall t, mentions_only t -> deep_ranked env p0 k t = true -> refs_in R t.
Proof.
    intros R p0 k HR. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hm Hd; simpl in Hm, Hd |- *; try exact I.
    - induction args as [|a args IHa]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd.
      destruct Hm as [Ha Has]. exact (conj (IH a Ha (proj1 Hd)) (IHa Has (proj2 Hd))).
    - exact (IH n Hm Hd).
    - destruct Hm as [Hp [Hv _]]. apply HR; [exact Hp|exact Hv|].
      destruct (deep_ranked_param env p0 k g Hd) as [E|Hr]; [right; exact E|left; exact Hr].
    - destruct Hm as [Ho Hn]. exact (conj (ownership_bound_caller o Ho) (IH n Hn Hd)).
    - induction cs as [|c cs IHc]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd.
      destruct Hm as [Hc Hcs]. exact (conj (IH c Hc (proj1 Hd)) (IHc Hcs (proj2 Hd))).
Qed.

(* The type parameters of the caller have bindings, also those in their declared bounds *)
Lemma caller_has_binding: forall g, In (param_of g) ps -> has_binding env b g = true.
Proof.
    intros g Hp. destruct (Hwithin _ Hp) as [o [x [Ex [Ho _]]]]. unfold has_binding. rewrite Ex, Ho.
    exact (in_fragment_is_gfrag env x (Hbf _ o x Ex)).
Qed.

Lemma caller_bex: forall t, mentions_only t -> bex env b t = true.
Proof.
    assert (Hlift: forall p k U, (forall q, In q ps -> q = p \/ parameter_rank env q < k -> U q = true) ->
        forall t, mentions_only t -> deep_ranked env p k t = true -> bex_h env b U t = true).
    { intros p k U HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hm Hd; simpl in Hm, Hd |- *; try reflexivity.
      - induction args as [|a args IHa]; [reflexivity|]. simpl in Hd |- *. apply andb_true_iff in Hd. destruct Hm as [Ha Has].
        rewrite (IH a Ha (proj1 Hd)), (IHa Has (proj2 Hd)). reflexivity.
      - exact (IH n Hm Hd).
      - destruct Hm as [Hp [Hv _]]. rewrite (caller_has_binding g Hp), (HU _ Hp (deep_ranked_param env p k g Hd)).
        unfold no_type_variables. rewrite Hv. reflexivity.
      - destruct Hm as [Ho Hn]. rewrite (ownership_bound_caller o Ho). exact (IH n Hn Hd).
      - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hd |- *. apply andb_true_iff in Hd. destruct Hm as [Hc Hcs].
        rewrite (IH c Hc (proj1 Hd)), (IHc Hcs (proj2 Hd)). reflexivity. }
    assert (Hparam: forall q, In q ps -> param_bex env b q = true).
    { intros q. remember (parameter_rank env q) as r eqn:Er. revert q Er. induction r as [r IH] using lt_wf_ind. intros q -> Hq.
      unfold param_bex. rewrite (through_param_eq env (bex_h env b) true deep (bex_h_agree env b) q).
      destruct (Hdeclared q Hq) as [_ [_ Hm]]. rewrite Hbound in Hm.
      apply (Hlift q (parameter_rank env q)); [|exact Hm|apply deep].
      intros q' Hq' [->|Hr]; [unfold param_eqb; rewrite Nat.eqb_refl; reflexivity|].
      destruct (param_eqb q' q); [reflexivity|]. exact (IH _ Hr q' eq_refl Hq'). }
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hm; simpl in Hm |- *; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl. destruct Hm as [Ha Has]. rewrite (IH a Ha), (IHa Has). reflexivity.
    - exact (IH n Hm).
    - destruct Hm as [Hp [Hv _]]. rewrite (caller_has_binding g Hp), (Hparam _ Hp). unfold no_type_variables. rewrite Hv. reflexivity.
    - destruct Hm as [Ho Hn]. rewrite (ownership_bound_caller o Ho). exact (IH n Hn).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. destruct Hm as [Hc Hcs]. rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma refs_in_all: forall t, mentions_only t -> refs_in (fun g0 => In (param_of g0) ps /\ variables_of g0 = []) t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hm; simpl in Hm |- *; try exact I.
    - induction args as [|a args IHa]; [exact I|]. destruct Hm as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (IH n Hm).
    - destruct Hm as [Hp [Hv _]]. exact (conj Hp Hv).
    - destruct Hm as [Ho Hn]. exact (conj (ownership_bound_caller o Ho) (IH n Hn)).
    - induction cs as [|c cs IHc]; [exact I|]. destruct Hm as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

(* Where the references of R are bound with fuel K, and so are those in their effective bounds and in
   the declared bounds of their parameters, every type of references of R is bound in *)
Section Refs.

Variable d: nat.
Variable R: GenericRef -> Prop.
Hypothesis HR: forall g, R g -> binds_ref env b d [] g = true /\ variables_of g = [].
Hypothesis Hclose: forall g, R g -> refs_in R (effective_bound env g) /\ refs_in R (parameter_bound env (param_of g)).

Lemma refs_top: forall g, R g -> top_bound_in env b d [] g = true.
Proof.
    intros g. remember (rank_of env g) as n eqn:En. revert g En. induction n as [n IH] using lt_wf_ind. intros g -> Hr.
    rewrite (top_bound_in_eq env wf b d []). pose proof (proj1 (Hclose g Hr)) as Ht.
    pose proof (effective_bound_ranked env ranked g) as Hrk. revert Ht Hrk. generalize (effective_bound env g) as t.
    fix IHt 1. intros [m c args|n|q|me msg|v o n|q|cs] Ht Hrk; simpl in Ht, Hrk |- *; try reflexivity.
    - exact (IHt n Ht Hrk).
    - destruct (HR q Ht) as [Hq Hv]. rewrite Hq. unfold no_type_variables. rewrite Hv.
      exact (IH _ (ref_ranked env _ q Hrk) q eq_refl Ht).
    - exact (IHt n (proj2 Ht) Hrk).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hrk |- *. apply andb_true_iff in Hrk. destruct Ht as [Hc Hcs].
      rewrite (IHt c Hc (proj1 Hrk)), (IHc Hcs (proj2 Hrk)). reflexivity.
Qed.

Lemma refs_param: forall g, R g -> param_bound_in env b d [] (param_of g) = true.
Proof.
    assert (H: forall n p, parameter_rank env p = n -> (exists g, R g /\ param_of g = p) -> param_bound_in env b d [] p = true).
    { induction n as [n IH] using lt_wf_ind. intros p En [r0 [Hr0 Ep]].
      unfold param_bound_in. rewrite (through_param_eq env (bound_in_h env b d []) true deep (bound_in_h_agree env b d []) p).
      pose proof (proj2 (Hclose r0 Hr0)) as Ht. rewrite Ep in Ht. pose proof (deep p) as Hd.
      revert Ht Hd. generalize (parameter_bound env p) as t.
      fix IHt 1. intros [m c args|n'|q|me msg|v o n'|q|cs] Ht Hd; simpl in Ht, Hd |- *; try reflexivity.
      - induction args as [|a args IHa]; [reflexivity|]. simpl in Hd |- *. apply andb_true_iff in Hd. destruct Ht as [Ha Has].
        rewrite (IHt a Ha (proj1 Hd)), (IHa Has (proj2 Hd)). reflexivity.
      - exact (IHt n' Ht Hd).
      - destruct (HR q Ht) as [Hq Hv]. rewrite Hq, (refs_top q Ht). unfold no_type_variables. rewrite Hv. cbn [andb].
        destruct (deep_ranked_param env p _ q Hd) as [Eq|Hr]; [rewrite Eq; unfold param_eqb; rewrite Nat.eqb_refl; reflexivity|].
        destruct (param_eqb (param_of q) p); [reflexivity|]. rewrite En in Hr. exact (IH _ Hr (param_of q) eq_refl (ex_intro _ q (conj Ht eq_refl))).
      - destruct Ht as [Ho Hn]. rewrite Ho. exact (IHt n' Hn Hd).
      - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hd |- *. apply andb_true_iff in Hd. destruct Ht as [Hc Hcs].
        rewrite (IHt c Hc (proj1 Hd)), (IHc Hcs (proj2 Hd)). reflexivity. }
    intros g Hr. exact (H _ (param_of g) eq_refl (ex_intro _ g (conj Hr eq_refl))).
Qed.

Lemma refs_bound_in: forall t, refs_in R t -> bound_in env b d [] t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl. destruct Ht as [Ha Has]. rewrite (IH a Ha), (IHa Has). reflexivity.
    - exact (IH n Ht).
    - destruct (HR g Ht) as [Hg Hv]. rewrite Hg, (refs_top g Ht), (refs_param g Ht). unfold no_type_variables. rewrite Hv. reflexivity.
    - destruct Ht as [Ho Hn]. rewrite Ho. exact (IH n Hn).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. destruct Ht as [Hc Hcs]. rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

End Refs.

Lemma uniform_fuel: forall {T: Type} (l: list T) (Q: nat -> T -> Prop),
    (forall n n' x, n <= n' -> Q n x -> Q n' x) -> (forall x, In x l -> exists n, Q n x) ->
    exists n, forall x, In x l -> Q n x.
Proof.
    intros T l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

Lemma binds_ref_mono: forall d d' g, d <= d' -> binds_ref env b d [] g = true -> binds_ref env b d' [] g = true.
Proof.
    intros d d' g Hle Hb. unfold binds_ref in Hb |- *.
    destruct (lookup_binding b (param_of g)) as [[| | | |[] o x| |]|]; try discriminate Hb.
    apply andb_true_iff in Hb. destruct Hb as [Hox Hb]. rewrite Hox. exact (respects_mono d d' _ _ Hle Hb).
Qed.

(* The mutabilities and `!` a reference may be given *)
Definition shapes: list (option Mutability * bool) :=
    [(None, false); (None, true)] ++ flat_map (fun m => [(Some m, false); (Some m, true)]) [exclusive; immutable; readonly; mutable].

Lemma shapes_complete: forall gm nn, In (gm, nn) shapes.
Proof. intros [[]|] []; simpl; tauto. Qed.

(* Every reference to a type parameter of the caller, of any mutability and `!`, is within its
   bound, instantiated: by the rank of the parameter. The parameter written plainly is, as Kotlin
   checks it; then the declared bound is bound in, by the lower ranks; and so the others are *)
Lemma param_refs: forall p, In p ps -> exists d, forall gm nn, binds_ref env b d [] (mkGenericRef gm nn p []) = true.
Proof.
    intros p. remember (parameter_rank env p) as n eqn:En. revert p En. induction n as [n IH] using lt_wf_ind. intros p -> Hp.
    set (lower := filter (fun q => Nat.ltb (parameter_rank env q) (parameter_rank env p)) ps).
    destruct (uniform_fuel lower (fun d q => forall gm nn, binds_ref env b d [] (mkGenericRef gm nn q []) = true)) as [KL HKL].
    { intros n'' f' q Hle H gm nn. exact (binds_ref_mono n'' f' _ Hle (H gm nn)). }
    { intros q Hq. apply filter_In in Hq. destruct Hq as [Hq Hr]. apply Nat.ltb_lt in Hr. exact (IH _ Hr q eq_refl Hq). }
    destruct (Hwithin p Hp) as [o [x [Ex [Ho [f0 Hf0]]]]]. pose proof (Hbf _ o x Ex) as Hx.
    destruct (Hdeclared p Hp) as [HtD [_ HmD]].
    set (K2 := max KL f0).
    (* the references to parameters of lower ranks, which are at the top of the declared bound *)
    set (L := fun r => In (param_of r) ps /\ variables_of r = [] /\ parameter_rank env (param_of r) < parameter_rank env p).
    assert (HL: forall q, In q ps -> parameter_rank env q < parameter_rank env p -> refs_in L (declared q)).
    { intros q Hq Hr. destruct (Hdeclared q Hq) as [_ [_ Hm]].
      apply (refs_in_from_mentions L q (parameter_rank env q)); [|exact Hm|rewrite Hbound; apply deep].
      intros r Hq2 Hv [Hr2|E]; [split; [exact Hq2|split; [exact Hv|lia]]|unfold L; rewrite E; split; [exact Hq|split; [exact Hv|exact Hr]]]. }
    assert (HLadj: forall gm nn gm' nn' q vs, L (mkGenericRef gm nn q vs) -> L (mkGenericRef gm' nn' q vs)) by (intros; assumption).
    assert (HRL: forall r, L r -> binds_ref env b K2 [] r = true /\ variables_of r = []).
    { intros [gm nn q vs] [Hq [Hv Hr]]. cbn [param_of variables_of] in Hq, Hv, Hr. subst vs. split; [|reflexivity].
      apply (binds_ref_mono KL); [unfold K2; lia|]. apply HKL. apply filter_In. split; [exact Hq|apply Nat.ltb_lt, Hr]. }
    assert (HcloseL: forall r, L r -> refs_in L (effective_bound env r) /\ refs_in L (parameter_bound env (param_of r))).
    { intros [gm nn q vs] [Hq [Hv Hr]]. cbn [param_of variables_of] in Hq, Hv, Hr |- *. subst vs.
      pose proof (HL q Hq Hr) as H1. rewrite Hbound in H1. split; [|exact H1].
      rewrite (effective_bound_eq env ranked). cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
      destruct (refs_in_adjust L HLadj _ H1) as [Hm Hn].
      destruct gm as [m|], nn; cbn iota; [exact (proj2 (refs_in_adjust L HLadj _ (Hm m)))|exact (Hm m)|exact Hn|exact H1]. }
    (* the declared bound: its type parameters have bindings, and at its top they are within their bounds *)
    assert (Hex: bex env b (declared p) = true) by exact (caller_bex _ HmD).
    assert (Htop: forall t, mentions_only t -> ranked_below env (parameter_rank env p) t = true ->
        bound_in_top_h env b K2 [] (top_bound_in env b K2 []) t = true).
    { fix IHt 1. intros [m c args|n'|q|me msg|v o' n'|q|cs] Hm Hr; simpl in Hm, Hr |- *; try reflexivity.
      - exact (IHt n' Hm Hr).
      - destruct Hm as [Hq [Hv _]].
        assert (Lq: L q) by (split; [exact Hq|split; [exact Hv|apply Nat.ltb_lt, Hr]]).
        destruct (HRL q Lq) as [Hb Hv']. rewrite Hb. unfold no_type_variables. rewrite Hv'.
        exact (refs_top K2 L HRL HcloseL q Lq).
      - exact (IHt n' (proj2 Hm) Hr).
      - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hr |- *. apply andb_true_iff in Hr. destruct Hm as [Hc Hcs].
        rewrite (IHt c Hc (proj1 Hr)), (IHc Hcs (proj2 Hr)). reflexivity. }
    assert (HtopD: bound_in_top_h env b K2 [] (top_bound_in env b K2 []) (declared p) = true)
        by (apply Htop; [exact HmD|rewrite Hbound; apply ranked]).
    (* any mutability and `!`: within the bound with them applied, by the instance of the declared bound *)
    assert (Hshape: forall gm nn, exists n'', binds_ref env b n'' [] (mkGenericRef gm nn p []) = true).
    { intros gm nn. set (g := mkGenericRef gm nn p []).
      assert (Heff: effective_bound env g = if nn then without_null env (match gm with Some m => with_mutability env m (declared p) | None => declared p end)
          else match gm with Some m => with_mutability env m (declared p) | None => declared p end)
          by (rewrite (effective_bound_eq env ranked), Hbound; reflexivity).
      destruct (instance_facts_ex env wf b K2 [] Hbf _ (declared p) (le_n _) HtD Hex HtopD) as [HcD [HmiD _]].
      assert (Hf: exists n'', unify env n'' (inst_nested env b (effective_bound env g)) (inst_ref env g x) (Ongoing []) = Some (Ongoing [])).
      { destruct gm as [m0|].
        - pose proof (inst_fit_in_fragment env g x Hx) as HZ.
          assert (HmZ: Model.is_subtype_of (assignment_mutability env (inst_fit env g x)) m0 = true)
              by exact (inst_fit_below_given g x m0 Hx eq_refl).
          destruct (cfrag_lower f0 _ x _ HcD Hx HZ (remut_inst_fit env g x Hx) (inst_fit_mutability_below env g x Hx) Hf0) as [f1 Hf1].
          destruct (within_adjust K2 (declared p) m0 nn _ HtD Hex HtopD HZ HmZ (ex_intro _ f1 Hf1)) as [n'' Hf].
          exists n''. rewrite Heff. unfold inst_ref. cbn [is_narrowed g]. destruct nn; exact Hf.
        - rewrite Heff. unfold inst_ref, inst_fit. cbn [is_narrowed given_mutability g].
          destruct nn; [|exists f0; exact Hf0].
          rewrite (narrow_instance_ex env wf b K2 [] Hbf _ HtD Hex HtopD).
          exists f0. exact (cfrag_without_null env wf f0 _ x [] [] HcD Hx Hf0). }
      destruct Hf as [n'' Hf]. exists n''.
      unfold binds_ref. cbn [param_of g]. rewrite Ex, Ho, (in_fragment_is_gfrag env x Hx). cbn [andb].
      unfold respects. rewrite Hf. reflexivity. }
    destruct (uniform_fuel shapes (fun d s => binds_ref env b d [] (mkGenericRef (fst s) (snd s) p []) = true)) as [d HK].
    { intros n'' f' s Hle H. exact (binds_ref_mono n'' f' _ Hle H). }
    { intros [gm nn] _. exact (Hshape gm nn). }
    exists d. intros gm nn. exact (HK (gm, nn) (shapes_complete gm nn)).
Qed.

(*
 * Every reference in a type, as GenericTypeReference makes them, to a type parameter of the caller,
 * is within its bound, instantiated (bound_in), where the type parameters are bound to types within
 * their declared bounds, instantiated
 *)
Theorem bound_in_derived: forall t, built t -> mentions_only t -> exists d, bound_in env b d [] t = true.
Proof.
    intros t _ Hm.
    destruct (uniform_fuel ps (fun d q => forall gm nn, binds_ref env b d [] (mkGenericRef gm nn q []) = true)) as [d HK].
    { intros n f' q Hle H gm nn. exact (binds_ref_mono n f' _ Hle (H gm nn)). }
    { exact param_refs. }
    exists d. set (R := fun r => In (param_of r) ps /\ variables_of r = []).
    apply (refs_bound_in d R); [| |exact (refs_in_all t Hm)].
    - intros [gm nn q vs] [Hq Hv]. cbn [param_of variables_of] in Hq, Hv. subst vs. exact (conj (HK q Hq gm nn) eq_refl).
    - intros [gm nn q vs] [Hq Hv]. cbn [param_of variables_of] in Hq, Hv |- *. subst vs.
      destruct (Hdeclared q Hq) as [_ [_ HmD]]. rewrite Hbound in HmD.
      split; [exact (refs_in_all _ (mentions_only_bound gm nn q HmD))|exact (refs_in_all _ HmD)].
Qed.

End Derivation.

End Bindings.

End WithinBounds.

From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import FinalValues.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Substitution, where unify terminates                                                           *)
(*                                                                                                *)
(* An intersection as the assignee is taken where one of its components is, the first one that is *)
(* (BoundIntersectionTypeReference.flippedUnify). With the type parameters instantiated, a        *)
(* component before that one, which was rejected, may be accepted, or rejected, or unify may go   *)
(* on without end on it: Kennedy and Pierce show that it may, with expansive inheritance. So the  *)
(* substitution lemma for intersections as assignees takes the form of never rejecting, as        *)
(* transitivity does in Generics.v (instances_never_fail); where unify terminates, that is the    *)
(* usual form (substitution_terminating). That unify terminates on the environment is the premise *)
(* unify_terminates_on of Conjectures.v, taken of the program at hand; Conjectures.v says what is  *)
(* known about which programs it holds for.                                                       *)
(*                                                                                                *)
(* ofComponents gives each component the mutability common to all of them, as which they are      *)
(* assigned: with a component of a const class, own, as all values are its objects                *)
(* (with_common_mutability). So, with S32 an I, `read I & U` takes `S32 & U`; with U bound to     *)
(* `mut Foo`, the instances are `mut I & mut Foo` and `S32 & own Foo`, the components of          *)
(* which it takes.                                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Section Terminating.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates_on env declared.

(* ---------------------------------------------------------------------------------------------- *)
(* The instances                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma cfrag_of_fragment: forall x, cfrag env x = true -> gfrag env x = true /\ refs_wf env declared x.
Proof.
    assert (Hi: forall ys, class_components env ys = true -> gfrag env (Intersection ys) = true /\ refs_wf env declared (Intersection ys)).
    { intros ys Hys. destruct (class_components_facts env ys Hys) as [Hl Hc]. split.
      - unfold class_components in Hys. apply andb_true_iff in Hys. destruct Hys as [_ Hu].
        apply (Fragment.make_intersection_gfrag env).
        + destruct ys; simpl in Hl; [lia|discriminate].
        + intros y Hy. destruct (Hc y Hy) as [Hcl Hf].
          split; [destruct y; first [reflexivity|discriminate Hcl]|exact (in_fragment_is_gfrag env y Hf)].
        + intros y Hy. apply internal_Mutability_dec_bl. exact (proj1 (forallb_forall _ _) Hu y Hy).
      - exact I. }
    intros x H. destruct (cfrag_cases env x H) as [Hx|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - split; [exact (in_fragment_is_gfrag env x Hx)|exact (proj1 (in_fragment_refs_wf env declared (depth x)) x (le_n _) Hx)].
    - exact (Hi ys Hys).
    - destruct (Hi ys Hys) as [Hg Hr]. split; [|exact Hr].
      change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true). rewrite Hg, andb_true_r.
      apply negb_true_iff. exact (class_components_not_nullable env ys Hys).
Qed.

Lemma cfrag_no_vars: forall x, cfrag env x = true -> no_vars x = true.
Proof. intros x H. exact (gfrag_no_vars env x (proj1 (cfrag_of_fragment x H))). Qed.

(* What unify accepts, it never rejects *)
Lemma accepted_never_fails: forall n x y, cfrag env x = true -> cfrag env y = true ->
    unify env n x y (Ongoing []) = Some (Ongoing []) -> never_fails env x y.
Proof. intros n x y Hx Hy H. exact (success_never_fails env wf n x y [] (cfrag_no_vars x Hx) (cfrag_no_vars y Hy) H). Qed.

(* A class type of a mutability below that of another, is taken where the other is *)
Lemma accepts_lower_mutability: forall n t x m s s', in_fragment env t = true -> in_fragment env x = true ->
    Model.is_subtype_of m (mutability_of env x) = true ->
    unify env n t x (Ongoing s) = Some (Ongoing s') -> unify env n t (with_mutability env m x) (Ongoing s) = Some (Ongoing s').
Proof.
    intros n t x m s s' HD Hx Hk H.
    apply (unify_remut env n t t x _ s s' (remut_refl env t HD) (remut_with_mutability env m x Hx)); [|exact H].
    pose proof (accepted_mutability_classes env n t x s s' HD Hx H) as Hm.
    exact (mutability_subtype_trans _ _ _ (with_mutability_below env m x Hx Hk) Hm).
Qed.

(* A type that never rejects a component of an intersection of class types, never rejects the
   intersection *)
Lemma never_fails_into_intersection: forall t ys y, in_fragment env t = true -> In y ys -> is_class y = true ->
    never_fails env t y -> never_fails env t (Intersection ys).
Proof.
    intros t ys y HD Hin Hy H. apply never_fails_step. intros f s.
    destruct (fragment_cases env t HD) as [[m [c [args ->]]]|[m [c [args [-> _]]]]].
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

Lemma never_fails_nullable: forall t A, never_fails env t A -> never_fails env (Nullable t) (Nullable A).
Proof. intros t A H. apply never_fails_step. intros f s. exact (H f s). Qed.

Lemma never_fails_nullable_intersection: forall t ys, is_nullable env (Intersection ys) = false ->
    never_fails env t (Intersection ys) -> never_fails env (Nullable t) (Intersection ys).
Proof.
    intros t ys Hn H. apply never_fails_step. intros f s.
    change (unify env (S f) (Nullable t) (Intersection ys) (Ongoing s)) with (unify env f t (without_null env (Intersection ys)) (Ongoing s)).
    rewrite (without_null_not_nullable_intersection env ys Hn). exact (H f s).
Qed.

Lemma never_fails_without_null: forall t ys, in_fragment env t = true -> is_nullable env (Intersection ys) = false ->
    never_fails env t (Intersection ys) -> never_fails env (without_null env t) (Intersection ys).
Proof.
    intros t ys HD Hn H f s. destruct (fragment_cases env t HD) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [exact (H f s)|].
    pose proof (H (S f) s) as H'.
    change (unify env (S f) (Nullable (RootResolved m c args)) (Intersection ys) (Ongoing s))
        with (unify env f (RootResolved m c args) (without_null env (Intersection ys)) (Ongoing s)) in H'.
    rewrite (without_null_not_nullable_intersection env ys Hn) in H'. exact H'.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What a type takes of an intersection                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* A non-null type of the fragment is its own `!` *)
Lemma tfrag_non_null_without_null: forall k t, sdepth t <= k -> tfrag env t = true -> is_nullable env t = false -> without_null env t = t.
Proof. intros k t _ _ Hn. exact (without_null_unchanged env t Hn). Qed.

Lemma narrow_non_null: forall g, generic_sfrag env g -> is_nullable env (effective_bound env g) = false -> narrow_ref env g = g.
Proof.
    intros [gm nn p vs] _ Hn. unfold narrow_ref. cbn [given_mutability is_narrowed param_of variables_of].
    rewrite (nullable_generic env wf (mkGenericRef gm nn p vs)), Hn, orb_false_r. reflexivity.
Qed.

(* A nullable type takes a component where the type in it does *)
Lemma nullable_takes_component: forall n t0 x s u, is_component_shape env x = true -> sfrag env x = true ->
    unify env n t0 x (Ongoing s) = u -> unify env (S n) (Nullable t0) x (Ongoing s) = u.
Proof.
    intros n t0 x s u Hsh Hc H. destruct x as [m d args| |g| | | |]; try discriminate Hsh.
    - rewrite unify_nullable_class. exact H.
    - rewrite unify_nullable_generic_step. apply (sfrag_generic_iff env wf) in Hc.
      pose proof (component_non_null env _ Hsh) as Hn. rewrite (nullable_generic env wf) in Hn.
      rewrite (narrow_non_null g Hc Hn). exact H.
Qed.

(* A type that takes an intersection takes one of its components *)
Lemma component_taken: forall n t cs s s', sfrag env t = true -> components_sfrag env cs = true ->
    unify env n t (Intersection cs) (Ongoing s) = Some (Ongoing s') ->
    exists C, In C cs /\ unify env n t C (Ongoing s) = Some (Ongoing s').
Proof.
    intros n t cs s s' Ht Hcs H. destruct (components_sfrag_facts env cs Hcs) as [_ Hc]. destruct n as [|n]; [discriminate H|].
    destruct (sfrag_cases env wf t Ht) as [[m [ct [args [-> _]]]]|[[m_bot ->]|[[m [ct [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]].
    1,2,4: destruct (unify_into_components env n _ cs s s' H eq_refl) as [C [Hin Hi]];
           exists C; split; [exact Hin|apply (unify_fuel_monotone env n); [lia|exact Hi]].
    - change (unify env (S n) (Nullable (RootResolved m ct args)) (Intersection cs) (Ongoing s))
          with (unify env n (RootResolved m ct args) (without_null env (Intersection cs)) (Ongoing s)) in H.
          rewrite (components_sfrag_without_null env cs Hcs) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_into_components env n _ cs s s' H eq_refl) as [C [Hin Hi]]. exists C. split; [exact Hin|].
      destruct (Hc C Hin) as [Hsh Hsc]. apply (unify_fuel_monotone env (S n)); [lia|].
      exact (nullable_takes_component n _ C s _ Hsh Hsc Hi).
    - change (unify env (S n) (Nullable (Generic g)) (Intersection cs) (Ongoing s))
          with (unify env n (Generic g) (without_null env (Intersection cs)) (Ongoing s)) in H.
          rewrite (components_sfrag_without_null env cs Hcs) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_into_components env n _ cs s s' H eq_refl) as [C [Hin Hi]]. exists C. split; [exact Hin|].
      destruct (Hc C Hin) as [Hsh Hsc]. apply (unify_fuel_monotone env (S n)); [lia|].
      exact (nullable_takes_component n _ C s _ Hsh Hsc Hi).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Substitution                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Variable b: Bindings.
Variable d1 d0: nat.
Hypothesis HE2: 2 <= d0.
Hypothesis HE: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= d0.
Hypothesis Hbf: bindings_in_fragment env b.

Let Main := substitution_with_arguments env wf b d1 [] d0 HE2 HE Hbf.

Lemma components_non_null: forall cs, components_sfrag env cs = true -> bound_in env b d1 [] (Intersection cs) = true ->
    forall C, In C cs -> is_nullable env (inst_nested env b C) = false.
Proof.
    intros cs Hcs Hb C Hin. destruct (proj2 (components_sfrag_facts env cs Hcs) C Hin) as [Hsh Hs].
    apply (proj2 (proj2 (instance_facts env wf b d1 [] Hbf _ C (le_n _) (sfrag_tfrag env C Hs)
        (bound_in_component env b d1 [] cs C Hb Hin)))).
    apply component_non_null, Hsh.
Qed.

(* A type that takes an intersection: instantiated, it never rejects its instance *)
Lemma into_intersection_never_fails: forall n t cs s, tfrag env t = true -> components_sfrag env cs = true ->
    bound_in env b d1 [] t = true -> bound_in env b d1 [] (Intersection cs) = true ->
    unify env n t (Intersection cs) (Ongoing []) = Some (Ongoing s) ->
    never_fails env (inst_nested env b t) (inst_nested env b (Intersection cs)).
Proof.
    intros n t cs s Ht Hcs Hbt Hb H.
    destruct (components_sfrag_facts env cs Hcs) as [_ Hc].
    destruct (intersection_instance env wf b d1 [] Hbf cs Hcs Hb (components_non_null cs Hcs Hb)) as [Heq [Hcc Hcomp]].
    set (ys := map (with_mutability env (common_mutability env (map (inst_nested env b) cs))) (map (inst_nested env b) cs)) in *.
    (* a type of sfrag that takes a component, instantiated, takes the instance of the component *)
    assert (Htake: forall n' t' u', sfrag env t' = true -> bound_in env b d1 [] t' = true ->
        unify env n' t' (Intersection cs) (Ongoing []) = Some (Ongoing u') ->
        u' = [] /\ exists c, In c cs /\ unify env (n' * S (S d1) + d0) (inst_nested env b t')
            (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) (Ongoing [])
            = Some (Ongoing [])).
    { intros n' t' u' Ht' Hbt' H'. destruct (component_taken n' t' cs [] u' Ht' Hcs H') as [c [Hin Hi]].
      destruct (Hc c Hin) as [_ Hsc'].
      destruct (proj1 (Main n') t' c u' Ht' Hsc' Hbt' (bound_in_component env b d1 [] cs c Hb Hin) Hi) as [-> Hi'].
      split; [reflexivity|]. exists c. split; [exact Hin|]. destruct (Hcomp c Hin) as [Hf Hm].
      exact (accepts_lower_mutability _ _ _ _ _ _ (instance_in_fragment env wf b d1 [] Hbf t' Ht' Hbt') Hf Hm Hi'). }
    assert (Hys: forall c, In c cs -> In (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) ys
        /\ is_class (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) = true
        /\ in_fragment env (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) = true).
    { intros c Hin. assert (Hy: In (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) ys)
          by (apply in_map, in_map, Hin).
      split; [exact Hy|]. exact (proj2 (class_components_facts env ys Hcc) _ Hy). }
    (* an intersection that takes the intersection *)
    assert (Hinter: forall n' ts u', components_sfrag env ts = true -> bound_in env b d1 [] (Intersection ts) = true ->
        unify env n' (Intersection ts) (Intersection cs) (Ongoing []) = Some (Ongoing u') ->
        never_fails env (inst_nested env b (Intersection ts)) (Intersection ys)).
    { intros n' ts u' Hts Hbts H'. destruct (components_sfrag_facts env ts Hts) as [Hlt Hct].
      destruct n' as [|n']; [discriminate H'|].
      assert (Hk: forall t' w, In t' ts -> unify env n' t' (Intersection cs) (Ongoing []) = Some (Ongoing w) -> w = []).
      { intros t' w Hin E'. destruct (Hct t' Hin) as [_ Hs'].
        exact (proj1 (Htake n' t' w Hs' (bound_in_component env b d1 [] ts t' Hbts Hin) E')). }
      assert (Hnv: forall t', In t' ts -> is_type_variable t' = false).
      { intros t' Hin. destruct (Hct t' Hin) as [Hsh _]. destruct t'; first [reflexivity|discriminate Hsh]. }
      destruct (intersection_target env n' ts (Intersection cs) [] u' Hnv ltac:(intros ->; simpl in Hlt; lia) I Hk H') as [_ Hall].
      (* each component of ts takes a component of cs *)
      assert (Hcomp_t: forall t', In t' ts -> exists c, In c cs /\ unify env (n' * S (S d1) + d0) (inst_nested env b t')
          (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) (Ongoing [])
          = Some (Ongoing [])).
      { intros t' Hin. destruct (Hct t' Hin) as [_ Hs'].
        exact (proj2 (Htake n' t' [] Hs' (bound_in_component env b d1 [] ts t' Hbts Hin) (Hall t' Hin))). }
      destruct (intersection_instance env wf b d1 [] Hbf ts Hts Hbts (components_non_null ts Hts Hbts)) as [Heqt [Hcct Hcompt]].
      rewrite Heqt. apply (inter_target_never_fails env wf).
      - apply forallb_forall. intros y Hy. apply cfrag_no_vars, in_fragment_cfrag.
        exact (proj2 (proj2 (class_components_facts env _ Hcct) y Hy)).
      - apply cfrag_no_vars. exact Hcc.
      - exact I.
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [t' [<- Hin]].
        destruct (Hcomp_t t' Hin) as [c [Hinc Hi]]. destruct (Hys c Hinc) as [Hyc [Hcl Hfy]].
        destruct (Hcompt t' Hin) as [Hft _].
        apply (never_fails_into_intersection _ ys _ (in_fragment_with_mutability env _ _ Hft) Hyc Hcl).
        apply (accepted_never_fails (n' * S (S d1) + d0)); [apply in_fragment_cfrag, in_fragment_with_mutability, Hft|apply in_fragment_cfrag, Hfy|].
        apply (accepts_with_mutability env); [exact Hft|exact Hfy| |exact Hi].
        (* the mutability common to the instances of cs is below that of each instance of ts *)
        rewrite (with_common_mutability env _ _ (in_map _ _ _ Hinc) (proj1 (Hcomp c Hinc))).
        apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
        intros m Hm. apply in_map_iff in Hm. destruct Hm as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [t'' [<- Hin'']].
        destruct (Hcomp_t t'' Hin'') as [c' [Hinc' Hi']]. destruct (Hys c' Hinc') as [_ [_ Hfy']].
        destruct (Hcompt t'' Hin'') as [Hft' _].
        pose proof (accepted_mutability_classes env _ _ _ _ _ Hft' Hfy' Hi') as Hm'.
        rewrite (with_common_mutability env _ _ (in_map _ _ _ Hinc') (proj1 (Hcomp c' Hinc'))) in Hm'. exact Hm'. }
    rewrite Heq. fold ys.
    destruct (tfrag_cases env t Ht) as [Hs|[[ts [-> Hts]]|[ts [-> Hts]]]].
    - destruct (Htake n t s Hs Hbt H) as [_ [c [Hin Hi]]]. destruct (Hys c Hin) as [Hyc [Hcl Hfy]].
      pose proof (instance_in_fragment env wf b d1 [] Hbf t Hs Hbt) as HT.
      apply (never_fails_into_intersection _ ys _ HT Hyc Hcl).
      exact (accepted_never_fails _ _ _ (in_fragment_cfrag env _ HT) (in_fragment_cfrag env _ Hfy) Hi).
    - exact (Hinter n ts s Hts Hbt H).
    - destruct n as [|n]; [discriminate H|].
      change (unify env (S n) (Nullable (Intersection ts)) (Intersection cs) (Ongoing []))
          with (unify env n (Intersection ts) (without_null env (Intersection cs)) (Ongoing [])) in H.
      rewrite (components_sfrag_without_null env cs Hcs) in H.
      pose proof (Hinter n ts s Hts Hbt H) as Hnf.
      destruct (intersection_instance env wf b d1 [] Hbf ts Hts Hbt (components_non_null ts Hts Hbt)) as [Heqt _].
      change (inst_nested env b (Nullable (Intersection ts))) with (rewrap_nullable (inst_nested env b (Intersection ts))).
      rewrite Heqt in Hnf |- *. exact (never_fails_nullable_intersection _ ys (class_components_not_nullable env ys Hcc) Hnf).
Qed.

(* With the type parameters instantiated, what unify accepted it never rejects *)
Lemma instances_never_fail: forall n t a s, tfrag env t = true -> tfrag env a = true ->
    bound_in env b d1 [] t = true -> bound_in env b d1 [] a = true ->
    unify env n t a (Ongoing []) = Some (Ongoing s) ->
    never_fails env (inst_nested env b t) (inst_nested env b a).
Proof.
    intros n t a s Ht Ha Hbt Hba H.
    destruct (tfrag_cases env a Ha) as [Hsa|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - (* no intersection as the assignee: accepted *)
      pose proof (proj1 (instance_facts env wf b d1 [] Hbf _ t (le_n _) Ht Hbt)) as HT.
      pose proof (proj1 (instance_facts env wf b d1 [] Hbf _ a (le_n _) Ha Hba)) as HA.
      destruct (tfrag_cases env t Ht) as [Hst|[[ts [-> Hts]]|[ts [-> Hts]]]].
      + destruct (proj1 (Main n) t a s Hst Hsa Hbt Hba H) as [-> Hi]. exact (accepted_never_fails _ _ _ HT HA Hi).
      + destruct n as [|n]; [discriminate H|].
        destruct (substitution_into_intersection env wf b d1 [] d0 HE2 HE Hbf n ts a s Hts Hsa Hbt Hba H) as [-> Hi].
        exact (accepted_never_fails _ _ _ HT HA Hi).
      + destruct n as [|n]; [discriminate H|].
        destruct (substitution_into_nullable_intersection env wf b d1 [] d0 HE2 HE Hbf n ts a s Hts Hsa Hbt Hba H) as [-> Hi].
        exact (accepted_never_fails _ _ _ HT HA Hi).
    - exact (into_intersection_never_fails n t cs s Ht Hcs Hbt Hba H).
    - (* a nullable intersection: what takes it is nullable *)
      change (bound_in env b d1 [] (Nullable (Intersection cs))) with (bound_in env b d1 [] (Intersection cs)) in Hba.
      destruct (intersection_instance env wf b d1 [] Hbf cs Hcs Hba (components_non_null cs Hcs Hba)) as [Heq [Hcc0 _]].
      change (inst_nested env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection cs))).
      destruct n as [|n]; [discriminate H|].
      destruct (tfrag_cases env t Ht) as [Hst|[[ts [-> Hts]]|[ts [-> Hts]]]].
      + destruct (sfrag_cases env wf t Hst) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> Ht0]]]]|[[g [-> _]]|[g [-> Hg]]]]]];
            unfold bottom_type in *; try (rewrite unify_class_nullable in H; discriminate H);
            try (rewrite (unify_generic_nullable env) in H; discriminate H);
            rewrite unify_nullable_nullable in H.
        * pose proof (into_intersection_never_fails n _ cs s (sfrag_tfrag env _ Ht0) Hcs Hbt Hba H) as Hnf.
          rewrite Heq in Hnf |- *. exact (never_fails_nullable _ _ Hnf).
        * change (bound_in env b d1 [] (Nullable (Generic g))) with (bound_in env b d1 [] (Generic g)) in Hbt.
          pose proof (into_intersection_never_fails n _ cs s (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg)) Hcs Hbt Hba H) as Hnf.
          destruct (binds_ref_some env wf b d1 [] g Hbt) as [o [x [Ex _]]].
          pose proof (inst_ref_in_fragment env g x (Hbf _ o x Ex)) as HI.
          rewrite (inst_nested_generic env b g _ o x Ex) in Hnf. rewrite (inst_nested_nullable_generic env b g _ o x Ex).
          rewrite (rewrap_without_null env _ HI). rewrite Heq in Hnf |- *.
          exact (never_fails_nullable _ _ (never_fails_without_null _ _ HI (class_components_not_nullable env _ Hcc0) Hnf)).
      + rewrite (unify_not_nullable_intersection env n ts _ [] (components_sfrag_not_nullable env ts Hts)) in H.
        discriminate H.
      + rewrite unify_nullable_nullable in H.
        change (bound_in env b d1 [] (Nullable (Intersection ts))) with (bound_in env b d1 [] (Intersection ts)) in Hbt.
        pose proof (into_intersection_never_fails n _ cs s (Hts : tfrag env (Intersection ts) = true) Hcs Hbt Hba H) as Hnf.
        destruct (intersection_instance env wf b d1 [] Hbf ts Hts Hbt (components_non_null ts Hts Hbt)) as [Heqt _].
        change (inst_nested env b (Nullable (Intersection ts))) with (rewrap_nullable (inst_nested env b (Intersection ts))).
        rewrite Heqt in Hnf |- *. rewrite Heq in Hnf |- *. exact (never_fails_nullable _ _ Hnf).
Qed.

(*
 * The substitution lemma, intersections as assignees included: within the fragment, a type that is
 * assignable to another stays so, with the type parameters in both instantiated exactly, where unify
 * terminates on the environment (unify_terminates_on, Conjectures.v).
 *)
Theorem substitution_terminating: forall fuel t a,
    tfrag env t = true -> tfrag env a = true -> bound_in env b d1 [] t = true -> bound_in env b d1 [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    exists n, is_assignable_to env n (instantiate env b a) (instantiate env b t) = Some true.
Proof.
    intros fuel t a Ht Ha Hbt Hba H.
    rewrite <- (inst_nested_instantiate env wf b d1 [] t Ht Hbt), <- (inst_nested_instantiate env wf b d1 [] a Ha Hba).
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    pose proof (instances_never_fail fuel t a u Ht Ha Hbt Hba Eu) as Hnf.
    pose proof (proj1 (instance_facts env wf b d1 [] Hbf _ t (le_n _) Ht Hbt)) as HT.
    pose proof (proj1 (instance_facts env wf b d1 [] Hbf _ a (le_n _) Ha Hba)) as HA.
    destruct (accepts env wf declared declared_wf terminates _ _
        (cfrag_of_fragment _ HA) (cfrag_of_fragment _ HT) Hnf) as [n Hf].
    exists n. rewrite Hf. reflexivity.
Qed.

End Terminating.

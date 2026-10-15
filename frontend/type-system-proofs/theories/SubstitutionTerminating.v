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
(* usual form (substitution_terminating). That unify terminates is the conjecture                 *)
(* unify_terminates of Conjectures.v. It rests on inheritance not being expansive, which the      *)
(* frontend enforces: findExpansiveSupertypes in                                                  *)
(* compiler/binding/basetype/ExpansiveInheritance.kt rejects the programs it would not hold for.  *)
(*                                                                                                *)
(* ofComponents gives each component the mutability common to all of them, as which they are      *)
(* assigned: with a component of a const class, exclusive, as all values are its objects          *)
(* (with_common_mutability). So, with S32 an I, `read I & U` takes `S32 & U`; with U bound to     *)
(* `mut Foo`, the instances are `mut I & mut Foo` and `S32 & exclusive Foo`, the components of    *)
(* which it takes.                                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Section Terminating.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.

(* ---------------------------------------------------------------------------------------------- *)
(* The instances                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma cfrag_of_fragment: forall x, cfrag env x = true -> gfrag env x = true /\ refs_wf env declared x.
Proof.
    assert (Hi: forall ys, class_components env ys = true -> gfrag env (Intersection ys) = true /\ refs_wf env declared (Intersection ys)).
    { intros ys Hys. destruct (class_components_facts env ys Hys) as [Hl Hc]. split.
      - simpl. apply andb_true_iff. split; [destruct ys; simpl in Hl |- *; [lia|reflexivity]|].
        apply forallb_forall. intros y Hy. destruct (Hc y Hy) as [Hcl Hf]. apply andb_true_iff.
        split; [destruct y; first [reflexivity|discriminate Hcl]|exact (in_fragment_is_gfrag env y Hf)].
      - exact I. }
    intros x H. destruct (cfrag_cases env x H) as [Hx|[[ys [-> Hys]]|[ys [-> Hys]]]].
    - split; [exact (in_fragment_is_gfrag env x Hx)|exact (proj1 (in_fragment_refs_wf env declared (depth x)) x (le_n _) Hx)].
    - exact (Hi ys Hys).
    - exact (Hi ys Hys).
Qed.

Lemma cfrag_no_vars: forall x, cfrag env x = true -> no_vars x = true.
Proof. intros x H. exact (gfrag_no_vars env x (proj1 (cfrag_of_fragment x H))). Qed.

(* What unify accepts, it never rejects *)
Lemma accepted_never_fails: forall f x y, cfrag env x = true -> cfrag env y = true ->
    unify env f x y (Ongoing []) = Some (Ongoing []) -> never_fails env x y.
Proof. intros f x y Hx Hy H. exact (success_never_fails env wf f x y [] (cfrag_no_vars x Hx) (cfrag_no_vars y Hy) H). Qed.

(* A class type of a mutability below that of another, is taken where the other is *)
Lemma accepts_lower_mutability: forall f D x k s r, in_fragment env D = true -> in_fragment env x = true ->
    Model.is_subtype_of k (mutability_of env x) = true ->
    unify env f D x (Ongoing s) = Some (Ongoing r) -> unify env f D (with_mutability env k x) (Ongoing s) = Some (Ongoing r).
Proof.
    intros f D x k s r HD Hx Hk H.
    apply (unify_remut env f D D x _ s r (remut_refl env D HD) (remut_with_mutability env k x Hx)); [|exact H].
    pose proof (accepted_mutability_classes env f D x s r HD Hx H) as Hm.
    exact (mutability_subtype_trans _ _ _ (with_mutability_below env k x Hx Hk) Hm).
Qed.

(* A type that never rejects a component of an intersection of class types, never rejects the
   intersection *)
Lemma never_fails_into_intersection: forall D ys y, in_fragment env D = true -> In y ys -> is_class y = true ->
    never_fails env D y -> never_fails env D (Intersection ys).
Proof.
    intros D ys y HD Hin Hy H. apply never_fails_step. intros f s.
    destruct (fragment_cases env D HD) as [[m [c [args ->]]]|[m [c [args [-> _]]]]].
    - exact (flipped_never_fails env f _ ys s y Hin (H f s)).
    - change (unify env (S f) (Nullable (RootResolved m c args)) (Intersection ys) (Ongoing s))
          with (unify env f (RootResolved m c args) (Intersection ys) (Ongoing s)).
      destruct f as [|f]; [discriminate|].
      apply (flipped_never_fails env f _ ys s y Hin).
      destruct y as [my cy argsy| | | | | |]; try discriminate Hy.
      pose proof (H (S f) s) as H'. rewrite unify_nullable_class in H'. exact H'.
Qed.

Lemma never_fails_nullable: forall T A, never_fails env T A -> never_fails env (Nullable T) (Nullable A).
Proof. intros T A H. apply never_fails_step. intros f s. exact (H f s). Qed.

Lemma never_fails_nullable_intersection: forall T ys,
    never_fails env T (Intersection ys) -> never_fails env (Nullable T) (Intersection ys).
Proof. intros T ys H. apply never_fails_step. intros f s. exact (H f s). Qed.

Lemma never_fails_without_null: forall D ys, in_fragment env D = true ->
    never_fails env D (Intersection ys) -> never_fails env (without_null env D) (Intersection ys).
Proof.
    intros D ys HD H f s. destruct (fragment_cases env D HD) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; [exact (H f s)|].
    exact (H (S f) s).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What a type takes of an intersection                                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* A non-null type of the fragment is its own `!` *)
Lemma tfrag_non_null_without_null: forall k t, sdepth env t <= k -> tfrag env t = true -> is_nullable env t = false -> without_null env t = t.
Proof. intros k t _ _ Hn. exact (without_null_unchanged env t Hn). Qed.

Lemma narrow_non_null: forall g, generic_sfrag env g -> is_nullable env (effective_bound env g) = false -> narrow_ref env g = g.
Proof.
    intros [gm nn p vs] _ Hn. unfold narrow_ref. cbn [given_mutability is_narrowed param_of variables_of].
    rewrite (nullable_generic env wf (mkGenericRef gm nn p vs)), Hn, orb_false_r. reflexivity.
Qed.

(* A nullable type takes a component where the type in it does *)
Lemma nullable_takes_component: forall n t0 c s r, is_component_shape env c = true -> sfrag env c = true ->
    unify env n t0 c (Ongoing s) = r -> unify env (S n) (Nullable t0) c (Ongoing s) = r.
Proof.
    intros n t0 c s r Hsh Hc H. destruct c as [m d args| |g| | | |]; try discriminate Hsh.
    - rewrite unify_nullable_class. exact H.
    - rewrite unify_nullable_generic_step. apply (sfrag_generic_iff env wf) in Hc.
      pose proof (component_non_null env _ Hsh) as Hn. rewrite (nullable_generic env wf) in Hn.
      rewrite (narrow_non_null g Hc Hn). exact H.
Qed.

(* A type that takes an intersection takes one of its components *)
Lemma component_taken: forall n t cs s u, sfrag env t = true -> components_sfrag env cs = true ->
    unify env n t (Intersection cs) (Ongoing s) = Some (Ongoing u) ->
    exists c, In c cs /\ unify env n t c (Ongoing s) = Some (Ongoing u).
Proof.
    intros n t cs s u Ht Hcs H. destruct (components_sfrag_facts env cs Hcs) as [_ Hc]. destruct n as [|n]; [discriminate H|].
    destruct (sfrag_cases env wf t Ht) as [[m [ct [args [-> _]]]]|[->|[[m [ct [args [-> _]]]]|[[g [-> _]]|[g [-> _]]]]]].
    1,2,4: destruct (unify_into_components env n _ cs s u H eq_refl) as [c [Hin Hi]];
           exists c; split; [exact Hin|apply (unify_fuel_monotone env n); [lia|exact Hi]].
    - change (unify env (S n) (Nullable (RootResolved m ct args)) (Intersection cs) (Ongoing s))
          with (unify env n (RootResolved m ct args) (Intersection cs) (Ongoing s)) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_into_components env n _ cs s u H eq_refl) as [c [Hin Hi]]. exists c. split; [exact Hin|].
      destruct (Hc c Hin) as [Hsh Hsc]. apply (unify_fuel_monotone env (S n)); [lia|].
      exact (nullable_takes_component n _ c s _ Hsh Hsc Hi).
    - change (unify env (S n) (Nullable (Generic g)) (Intersection cs) (Ongoing s))
          with (unify env n (Generic g) (Intersection cs) (Ongoing s)) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_into_components env n _ cs s u H eq_refl) as [c [Hin Hi]]. exists c. split; [exact Hin|].
      destruct (Hc c Hin) as [Hsh Hsc]. apply (unify_fuel_monotone env (S n)); [lia|].
      exact (nullable_takes_component n _ c s _ Hsh Hsc Hi).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Substitution                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Variable b: Bindings.
Variable K E: nat.
Hypothesis HE2: 2 <= E.
Hypothesis HE: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> depth x <= E.
Hypothesis Hbf: bindings_in_fragment env b.

Let Main := substitution_with_arguments env wf b K [] E HE2 HE Hbf.

Lemma components_non_null: forall cs, components_sfrag env cs = true -> bound_in env b K [] (Intersection cs) = true ->
    forall c, In c cs -> is_nullable env (inst_nested env b c) = false.
Proof.
    intros cs Hcs Hb c Hin. destruct (proj2 (components_sfrag_facts env cs Hcs) c Hin) as [Hsh Hs].
    apply (proj2 (proj2 (instance_facts env wf b K [] Hbf _ c (le_n _) (sfrag_tfrag env c Hs)
        (bound_in_component env b K [] cs c Hb Hin)))).
    apply component_non_null, Hsh.
Qed.

(* A type that takes an intersection: instantiated, it never rejects its instance *)
Lemma into_intersection_never_fails: forall n t cs u, tfrag env t = true -> components_sfrag env cs = true ->
    bound_in env b K [] t = true -> bound_in env b K [] (Intersection cs) = true ->
    unify env n t (Intersection cs) (Ongoing []) = Some (Ongoing u) ->
    never_fails env (inst_nested env b t) (inst_nested env b (Intersection cs)).
Proof.
    intros n t cs u Ht Hcs Hbt Hb H.
    destruct (components_sfrag_facts env cs Hcs) as [_ Hc].
    destruct (intersection_instance env wf b K [] Hbf cs Hcs Hb (components_non_null cs Hcs Hb)) as [Heq [Hcc Hcomp]].
    set (ys := map (with_mutability env (common_mutability env (map (inst_nested env b) cs))) (map (inst_nested env b) cs)) in *.
    (* a type of sfrag that takes a component, instantiated, takes the instance of the component *)
    assert (Htake: forall n' t' u', sfrag env t' = true -> bound_in env b K [] t' = true ->
        unify env n' t' (Intersection cs) (Ongoing []) = Some (Ongoing u') ->
        u' = [] /\ exists c, In c cs /\ unify env (n' * S (S K) + E) (inst_nested env b t')
            (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) (Ongoing [])
            = Some (Ongoing [])).
    { intros n' t' u' Ht' Hbt' H'. destruct (component_taken n' t' cs [] u' Ht' Hcs H') as [c [Hin Hi]].
      destruct (Hc c Hin) as [_ Hsc'].
      destruct (proj1 (Main n') t' c u' Ht' Hsc' Hbt' (bound_in_component env b K [] cs c Hb Hin) Hi) as [-> Hi'].
      split; [reflexivity|]. exists c. split; [exact Hin|]. destruct (Hcomp c Hin) as [Hf Hm].
      exact (accepts_lower_mutability _ _ _ _ _ _ (instance_in_fragment env wf b K [] Hbf t' Ht' Hbt') Hf Hm Hi'). }
    assert (Hys: forall c, In c cs -> In (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) ys
        /\ is_class (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) = true
        /\ in_fragment env (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) = true).
    { intros c Hin. assert (Hy: In (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) ys)
          by (apply in_map, in_map, Hin).
      split; [exact Hy|]. exact (proj2 (class_components_facts env ys Hcc) _ Hy). }
    (* an intersection that takes the intersection *)
    assert (Hinter: forall n' ts u', components_sfrag env ts = true -> bound_in env b K [] (Intersection ts) = true ->
        unify env n' (Intersection ts) (Intersection cs) (Ongoing []) = Some (Ongoing u') ->
        never_fails env (inst_nested env b (Intersection ts)) (Intersection ys)).
    { intros n' ts u' Hts Hbts H'. destruct (components_sfrag_facts env ts Hts) as [Hlt Hct].
      destruct n' as [|n']; [discriminate H'|].
      assert (Hk: forall t' w, In t' ts -> unify env n' t' (Intersection cs) (Ongoing []) = Some (Ongoing w) -> w = []).
      { intros t' w Hin E'. destruct (Hct t' Hin) as [_ Hs'].
        exact (proj1 (Htake n' t' w Hs' (bound_in_component env b K [] ts t' Hbts Hin) E')). }
      assert (Hnv: forall t', In t' ts -> is_type_variable t' = false).
      { intros t' Hin. destruct (Hct t' Hin) as [Hsh _]. destruct t'; first [reflexivity|discriminate Hsh]. }
      destruct (intersection_target env n' ts (Intersection cs) [] u' Hnv ltac:(intros ->; simpl in Hlt; lia) I Hk H') as [_ Hall].
      (* each component of ts takes a component of cs *)
      assert (Hcomp_t: forall t', In t' ts -> exists c, In c cs /\ unify env (n' * S (S K) + E) (inst_nested env b t')
          (with_mutability env (common_mutability env (map (inst_nested env b) cs)) (inst_nested env b c)) (Ongoing [])
          = Some (Ongoing [])).
      { intros t' Hin. destruct (Hct t' Hin) as [_ Hs'].
        exact (proj2 (Htake n' t' [] Hs' (bound_in_component env b K [] ts t' Hbts Hin) (Hall t' Hin))). }
      destruct (intersection_instance env wf b K [] Hbf ts Hts Hbts (components_non_null ts Hts Hbts)) as [Heqt [Hcct Hcompt]].
      rewrite Heqt. apply (inter_target_never_fails env wf).
      - apply forallb_forall. intros y Hy. apply cfrag_no_vars, in_fragment_cfrag.
        exact (proj2 (proj2 (class_components_facts env _ Hcct) y Hy)).
      - apply cfrag_no_vars. exact Hcc.
      - exact I.
      - intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [t' [<- Hin]].
        destruct (Hcomp_t t' Hin) as [c [Hinc Hi]]. destruct (Hys c Hinc) as [Hyc [Hcl Hfy]].
        destruct (Hcompt t' Hin) as [Hft _].
        apply (never_fails_into_intersection _ ys _ (in_fragment_with_mutability env _ _ Hft) Hyc Hcl).
        apply (accepted_never_fails (n' * S (S K) + E)); [apply in_fragment_cfrag, in_fragment_with_mutability, Hft|apply in_fragment_cfrag, Hfy|].
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
    - destruct (Htake n t u Hs Hbt H) as [_ [c [Hin Hi]]]. destruct (Hys c Hin) as [Hyc [Hcl Hfy]].
      pose proof (instance_in_fragment env wf b K [] Hbf t Hs Hbt) as HT.
      apply (never_fails_into_intersection _ ys _ HT Hyc Hcl).
      exact (accepted_never_fails _ _ _ (in_fragment_cfrag env _ HT) (in_fragment_cfrag env _ Hfy) Hi).
    - exact (Hinter n ts u Hts Hbt H).
    - destruct n as [|n]; [discriminate H|].
      change (unify env (S n) (Nullable (Intersection ts)) (Intersection cs) (Ongoing []))
          with (unify env n (Intersection ts) (Intersection cs) (Ongoing [])) in H.
      pose proof (Hinter n ts u Hts Hbt H) as Hnf.
      destruct (intersection_instance env wf b K [] Hbf ts Hts Hbt (components_non_null ts Hts Hbt)) as [Heqt _].
      change (inst_nested env b (Nullable (Intersection ts))) with (rewrap_nullable (inst_nested env b (Intersection ts))).
      rewrite Heqt in Hnf |- *. exact (never_fails_nullable_intersection _ ys Hnf).
Qed.

(* With the type parameters instantiated, what unify accepted it never rejects *)
Lemma instances_never_fail: forall n t a u, tfrag env t = true -> tfrag env a = true ->
    bound_in env b K [] t = true -> bound_in env b K [] a = true ->
    unify env n t a (Ongoing []) = Some (Ongoing u) ->
    never_fails env (inst_nested env b t) (inst_nested env b a).
Proof.
    intros n t a u Ht Ha Hbt Hba H.
    destruct (tfrag_cases env a Ha) as [Hsa|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - (* no intersection as the assignee: accepted *)
      pose proof (proj1 (instance_facts env wf b K [] Hbf _ t (le_n _) Ht Hbt)) as HT.
      pose proof (proj1 (instance_facts env wf b K [] Hbf _ a (le_n _) Ha Hba)) as HA.
      destruct (tfrag_cases env t Ht) as [Hst|[[ts [-> Hts]]|[ts [-> Hts]]]].
      + destruct (proj1 (Main n) t a u Hst Hsa Hbt Hba H) as [-> Hi]. exact (accepted_never_fails _ _ _ HT HA Hi).
      + destruct n as [|n]; [discriminate H|].
        destruct (substitution_into_intersection env wf b K [] E HE2 HE Hbf n ts a u Hts Hsa Hbt Hba H) as [-> Hi].
        exact (accepted_never_fails _ _ _ HT HA Hi).
      + destruct n as [|n]; [discriminate H|].
        destruct (substitution_into_nullable_intersection env wf b K [] E HE2 HE Hbf n ts a u Hts Hsa Hbt Hba H) as [-> Hi].
        exact (accepted_never_fails _ _ _ HT HA Hi).
    - exact (into_intersection_never_fails n t cs u Ht Hcs Hbt Hba H).
    - (* a nullable intersection: what takes it is nullable *)
      change (bound_in env b K [] (Nullable (Intersection cs))) with (bound_in env b K [] (Intersection cs)) in Hba.
      destruct (intersection_instance env wf b K [] Hbf cs Hcs Hba (components_non_null cs Hcs Hba)) as [Heq _].
      change (inst_nested env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection cs))).
      destruct n as [|n]; [discriminate H|].
      destruct (tfrag_cases env t Ht) as [Hst|[[ts [-> Hts]]|[ts [-> Hts]]]].
      + destruct (sfrag_cases env wf t Hst) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> Ht0]]]]|[[g [-> _]]|[g [-> Hg]]]]]];
            unfold bottom_type in *; try (rewrite unify_class_nullable in H; discriminate H);
            try (rewrite (unify_generic_nullable env) in H; discriminate H);
            rewrite unify_nullable_nullable in H.
        * pose proof (into_intersection_never_fails n _ cs u (sfrag_tfrag env _ Ht0) Hcs Hbt Hba H) as Hnf.
          rewrite Heq in Hnf |- *. exact (never_fails_nullable _ _ Hnf).
        * change (bound_in env b K [] (Nullable (Generic g))) with (bound_in env b K [] (Generic g)) in Hbt.
          pose proof (into_intersection_never_fails n _ cs u (sfrag_tfrag env _ (generic_sfrag_sfrag env wf g Hg)) Hcs Hbt Hba H) as Hnf.
          destruct (binds_ref_some env wf b K [] g Hbt) as [o [x [Ex _]]].
          pose proof (inst_ref_in_fragment env g x (Hbf _ o x Ex)) as HI.
          rewrite (inst_nested_generic env b g _ o x Ex) in Hnf. rewrite (inst_nested_nullable_generic env b g _ o x Ex).
          rewrite (rewrap_without_null env _ HI). rewrite Heq in Hnf |- *.
          exact (never_fails_nullable _ _ (never_fails_without_null _ _ HI Hnf)).
      + change (unify env (S n) (Intersection ts) (Nullable (Intersection cs)) (Ongoing [])) with (Some (@Failed)) in H.
        discriminate H.
      + rewrite unify_nullable_nullable in H.
        change (bound_in env b K [] (Nullable (Intersection ts))) with (bound_in env b K [] (Intersection ts)) in Hbt.
        pose proof (into_intersection_never_fails n _ cs u (Hts : tfrag env (Intersection ts) = true) Hcs Hbt Hba H) as Hnf.
        destruct (intersection_instance env wf b K [] Hbf ts Hts Hbt (components_non_null ts Hts Hbt)) as [Heqt _].
        change (inst_nested env b (Nullable (Intersection ts))) with (rewrap_nullable (inst_nested env b (Intersection ts))).
        rewrite Heqt in Hnf |- *. rewrite Heq in Hnf |- *. exact (never_fails_nullable _ _ Hnf).
Qed.

(*
 * The substitution lemma, intersections as assignees included: within the fragment, a type that is
 * assignable to another stays so, with the type parameters in both instantiated exactly, where unify
 * terminates (unify_terminates, on inheritance that isn't expansive: ExpansiveInheritance.kt).
 *)
Theorem substitution_terminating: forall fuel t a,
    tfrag env t = true -> tfrag env a = true -> bound_in env b K [] t = true -> bound_in env b K [] a = true ->
    is_assignable_to env fuel a t = Some true ->
    exists f, is_assignable_to env f (instantiate env b a) (instantiate env b t) = Some true.
Proof.
    intros fuel t a Ht Ha Hbt Hba H.
    rewrite <- (inst_nested_instantiate env wf b K [] t Ht Hbt), <- (inst_nested_instantiate env wf b K [] a Ha Hba).
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env fuel t a (Ongoing [])) as [[u|]|] eqn:Eu; try discriminate H.
    pose proof (instances_never_fail fuel t a u Ht Ha Hbt Hba Eu) as Hnf.
    pose proof (proj1 (instance_facts env wf b K [] Hbf _ t (le_n _) Ht Hbt)) as HT.
    pose proof (proj1 (instance_facts env wf b K [] Hbf _ a (le_n _) Ha Hba)) as HA.
    destruct (accepts env wf declared declared_wf terminates finite not_expansive _ _
        (cfrag_of_fragment _ HA) (cfrag_of_fragment _ HT) Hnf) as [f Hf].
    exists f. rewrite Hf. reflexivity.
Qed.

End Terminating.

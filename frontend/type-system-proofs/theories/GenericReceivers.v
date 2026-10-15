From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import MemberCalls.
From EmergeTypeSystem Require Import FinalValues.
From EmergeTypeSystem Require Import SubstitutionWide.
From EmergeTypeSystem Require Import WithinBounds.
From EmergeTypeSystem Require Import GenericArguments.
From EmergeTypeSystem Require Import GenericCode.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Calls in generic code on receivers of the type parameters of the caller                        *)
(*                                                                                                *)
(* A receiver in generic code mentions the type parameters of the caller, too (`list.add(x)` with *)
(* `list: List<T>` in `fn f<T>`). Unifying the receiver parameter binds the type parameters of    *)
(* the class exactly to its type arguments (`T`), which relate to the type arguments of the       *)
(* object only once T is instantiated: at run time, the object is below the receiver,             *)
(* instantiated. So inference and instantiating go together here: what unify accepts of an        *)
(* argument for a parameter in generic code, the argument instantiated takes, with each type      *)
(* variable replaced by what it stands for at run time (rsat): a type the type argument it is     *)
(* bound to, instantiated, stands for, or, between its bounds, a type of generic code             *)
(* instantiated (runtime_arguments). The variable states and their monotonicity come from         *)
(* GenericArguments.v; the leaves take the substitution lemma of SubstitutionWide.v               *)
(* (subst_below). Calling a member function on such a receiver is then sound at run time          *)
(* (member_call_on_generic_receiver).                                                             *)
(*                                                                                                *)
(* The bounds of the type parameters of the function are class types without type parameters.     *)
(* ---------------------------------------------------------------------------------------------- *)

Section Receivers.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.
Hypothesis intersect_in_fragment: intersect_stays_in_fragment env declared.
Hypothesis supertype_in_fragment: closest_common_supertype_stays_in_fragment env declared.
Hypothesis intersect_below: intersect_is_below_both env declared.
Hypothesis supertype_above: closest_common_supertype_is_above_both env declared.
Hypothesis intersect_generic: intersect_stays_in_generic_code env declared.
Hypothesis supertype_generic: closest_common_supertype_stays_in_generic_code env declared.

(* The type parameters of the caller, and what they are bound to *)
Variable ps: list TypeParameterId.
Variable sigma: Bindings.
Hypothesis Hsf: bindings_in_fragment env sigma.
Hypothesis Hwithin: forall p, In p ps -> exists o x, lookup_binding sigma p = Some (TypeArgument Model.invariant o x)
    /\ is_exact_ownership o = true
    /\ exists f, unify env f (inst_nested env sigma (declared p)) x (Ongoing []) = Some (Ongoing []).
Hypothesis Hdeclared: forall p, In p ps -> tfrag env (declared p) = true /\ built env declared (declared p)
    /\ mentions_only env ps (declared p).

Let caller := caller_type env declared ps.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating the types of generic code                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma instance_ground: forall t, caller t ->
    exists K, bound_in env sigma K [] t = true /\ ground env (instantiate env sigma t) = true.
Proof.
    intros t [Hw [Hb Hm]]. destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) t Hb Hm) as [K HK].
    exists K. split; [exact HK|exact (proj1 (wide_instance env wf sigma K Hsf t Hw HK))].
Qed.

(* What is below a type in generic code is so, instantiated *)
Lemma subst_below: forall x y, caller x -> caller y -> below env x y ->
    exists f, unify env f (instantiate env sigma y) (instantiate env sigma x) (Ongoing []) = Some (Ongoing []).
Proof.
    intros x y Hx Hy [n H].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) x (proj1 (proj2 Hx)) (proj2 (proj2 Hx))) as [K1 HK1].
    destruct (bound_in_derived env wf sigma Hsf declared ps Hwithin Hdeclared (bw_declared env declared declared_wf) y (proj1 (proj2 Hy)) (proj2 (proj2 Hy))) as [K2 HK2].
    destruct (substitution_wide env declared sigma (max K1 K2) n y x wf declared_wf terminates finite not_expansive Hsf
        (proj1 Hy) (proj1 Hx) (bound_in_mono env wf sigma K2 (max K1 K2) _ (Nat.le_max_r K1 K2) HK2)
        (bound_in_mono env wf sigma K1 (max K1 K2) _ (Nat.le_max_l K1 K2) HK1)) as [f Hf].
    - unfold is_assignable_to, empty_unification. rewrite H. reflexivity.
    - destruct (instance_ground x Hx) as [? [_ Gx]]. destruct (instance_ground y Hy) as [? [_ Gy]].
      exists f. unfold is_assignable_to, empty_unification in Hf.
      destruct (unify env f (instantiate env sigma y) (instantiate env sigma x) (Ongoing [])) as [[u|]|] eqn:E; try discriminate Hf.
      rewrite <- E. rewrite (ground_keeps env wf f _ _ [] u Gy Gx E) in E. exact E.
Qed.

Lemma rtrans: forall X Y Z, ground env X = true -> ground env Y = true -> ground env Z = true ->
    (exists f, unify env f Y X (Ongoing []) = Some (Ongoing [])) -> (exists f, unify env f Z Y (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f Z X (Ongoing []) = Some (Ongoing []).
Proof.
    intros X Y Z HX HY HZ [f1 H1] [f2 H2].
    exact (ground_trans env wf declared declared_wf terminates finite not_expansive f1 f2 X Y Z HX HY HZ H1 H2).
Qed.

Lemma ground_takes_bottom: forall y, ground env y = true -> exists f, unify env f y bottom_type (Ongoing []) = Some (Ongoing []).
Proof.
    intros y Hy. exact (below_bottom env wf declared declared_wf terminates finite not_expansive y (ground_of_fragment env declared y Hy)).
Qed.

Lemma ground_below_top: forall y, ground env y = true -> exists f, unify env f top_type y (Ongoing []) = Some (Ongoing []).
Proof.
    intros y Hy. exact (below_top env wf declared declared_wf terminates finite not_expansive y (ground_of_fragment env declared y Hy)).
Qed.

Lemma caller_top': caller top_type.
Proof. exact (caller_top env wf declared ps). Qed.

Lemma caller_bottom': caller bottom_type.
Proof. exact (caller_bottom env declared ps). Qed.

Lemma ground_bottom: ground env bottom_type = true.
Proof. unfold ground. rewrite (bottom_gfrag env wf). reflexivity. Qed.

Lemma ground_top: ground env top_type = true.
Proof. unfold ground. rewrite (top_gfrag env wf). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What the type variables stand for at run time                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* A type the variable is replaced with at run time: one that the type argument it is bound to
   exactly, instantiated, stands for; or, between its bounds, a type of generic code, instantiated *)
Definition rfits (st: VariableState) (o: Ownership) (z: EType): Prop :=
    if is_exact st then
        exists vb ob X K, upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ of_fragment env declared X /\ caller X /\ (forall q, ob = parameter_ownership q -> In q ps)
            /\ unify env (S K) (instantiate env sigma (TypeArgument vb ob X)) (TypeArgument Model.invariant o z) (Ongoing [])
                = Some (Ongoing [])
    else exists x, of_fragment env declared x /\ caller x /\ gfits env declared st o x /\ z = instantiate env sigma x.

Definition rsat (b: Bindings) (s: VariableStates): Prop :=
    forall p o z, lookup_binding b p = Some (TypeArgument Model.invariant o z) -> exists st, lookup_state s p = Some st /\ rfits st o z.

Definition dom (b: Bindings) (s: VariableStates): Prop :=
    forall p o z, lookup_binding b p = Some (TypeArgument Model.invariant o z) -> exists st, lookup_state s p = Some st.

Let gwf := gwf_states env declared caller.

Lemma dom_forward: forall b s s', gwf s -> keeps_exact s s' -> dom b s -> dom b s'.
Proof.
    intros b s s' Hs [Hk1 Hk2] Hd p o z Hp. destruct (Hd p o z Hp) as [st Hl]. destruct (is_exact st) eqn:Ee.
    - exists st. exact (Hk1 p st Hl Ee).
    - destruct (proj1 Hs p st Hl) as [_ [_ Hw]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' _]]. exists st'. exact Hl'.
Qed.

(* What the variables stand for after a unification, they stand for before *)
Lemma rsat_back: forall b s s', gwf s -> keeps_exact s s' ->
    (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s) -> dom b s -> rsat b s' -> rsat b s.
Proof.
    intros b s s' Hs [Hk1 Hk2] Hmono Hdom H p o z Hp. destruct (Hdom p o z Hp) as [st Hl].
    destruct (H p o z Hp) as [st' [Hl' Hf']]. exists st. split; [exact Hl|].
    destruct (is_exact st) eqn:Ee.
    - rewrite (Hk1 p st Hl Ee) in Hl'. injection Hl' as <-. exact Hf'.
    - destruct (proj1 Hs p st Hl) as [_ [_ Hw]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st'' [Hl'' [He'' _]]]. rewrite Hl' in Hl''. injection Hl'' as <-.
      unfold rfits in Hf' |- *. rewrite He'' in Hf'. rewrite Ee. destruct Hf' as [x [Hx [Hc [Hg ->]]]].
      exists x. split; [exact Hx|]. split; [exact Hc|]. split; [|reflexivity].
      (* through the bindings of p alone *)
      assert (Hs1: gsatisfies env declared [(p, TypeArgument Model.invariant o x)] s').
      { intros q o' x' Hq. simpl in Hq. destruct (param_eqb q p) eqn:Eq; [|discriminate Hq]. apply param_eqb_eq in Eq. subst q.
        injection Hq as <- <-. split; [exact Hx|]. exists st'. split; [exact Hl'|exact Hg]. }
      destruct (Hmono _ Hs1 p o x) as [_ [st0 [Hl0 Hg0]]]; [simpl; rewrite param_eqb_refl; reflexivity|].
      rewrite Hl in Hl0. injection Hl0 as <-. exact Hg0.
Qed.

Lemma ownership_refl: forall o, ownership_is_assignable_to o o = true.
Proof. intros [| | |p]; [reflexivity..|apply param_eqb_refl]. Qed.

(* A variable bound exactly stands for the types the variance of its type argument allows, in the
   types of generic code *)
Lemma gfits_exact: forall st vb ob X x, is_exact st = true ->
    upper_bound st = TypeArgument vb ob X -> lower_bound st = TypeArgument vb ob X ->
    of_fragment env declared X -> of_fragment env declared x ->
    (exists K, compare_variances (unify env K) vb Model.invariant X x [] = Some (Ongoing [])) ->
    gfits env declared st ob x.
Proof.
    intros st vb ob X x He Hu Hl HX Hx [K Hc]. unfold gfits. rewrite He. exists vb, ob, X, K.
    split; [exact Hu|]. split; [exact Hl|]. split; [exact HX|]. split; [exact Hx|].
    rewrite (unify_type_arguments env K vb ob X Model.invariant ob x [] (gfrag_not_variable env X (proj1 HX))), ownership_refl.
    exact Hc.
Qed.

(* The type argument a variable is bound to exactly, instantiated *)
Lemma instance_of_argument: forall vb ob X, caller X -> (forall q, ob = parameter_ownership q -> In q ps) ->
    instantiate env sigma (TypeArgument vb ob X) = TypeArgument vb (instantiate_ownership sigma ob) (instantiate env sigma X)
    /\ ground env (instantiate env sigma X) = true.
Proof.
    intros vb ob X HcX Hob. destruct (instance_ground X HcX) as [KX [HbX HgX]].
    assert (HbTA: bound_in env sigma KX [] (TypeArgument vb ob X) = true).
    { cbn [bound_in]. rewrite HbX, andb_true_r. destruct ob as [| | |q]; try reflexivity.
      destruct (Hwithin q (Hob q eq_refl)) as [o' [x' [Ex' [Ho' _]]]]. cbn [ownership_bound]. rewrite Ex'. exact Ho'. }
    destruct (wide_argument env wf sigma KX Hsf (TypeArgument vb ob X) (proj1 HcX) HbTA) as [v' [o' [n' [E1 [E2 _]]]]].
    injection E1 as <- <- <-. split; [exact E2|exact HgX].
Qed.

(* What the variable takes, at run time *)
Lemma rtarget_leaf: forall n p bnd A s s', gwf s -> of_fragment env declared A -> bottom_only env A = true -> caller A ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    forall o z, ground env z = true -> (forall st', lookup_state s' p = Some st' -> rfits st' o z) ->
    exists f, unify env f z (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p bnd A s s' Hs HA HbA HcA H o z Hz Hfit.
    destruct (gtarget_leaf env wf declared declared_wf terminates finite not_expansive supertype_in_fragment supertype_above
        caller (supertype_generic ps) n p bnd A s s' Hs HA HbA HcA H) as [_ [_ Hsnd]].
    destruct (instance_ground A HcA) as [KA [_ HgA]].
    pose proof (variable_target_step env n p bnd A s s' (proj1 HA) H) as H'.
    unfold plus_supertype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: by the type argument, instantiated *)
      destruct (keeps_free env wf n _ A s s' (proj1 (proj2 (proj1 Hs p st Hl))) (of_fragment_no_vars env declared A HA) H') as [-> _].
      pose proof (Hfit st Hl) as Hf. unfold rfits in Hf. rewrite Ee in Hf.
      destruct Hf as [vb [ob [X [K [Hu [Hlo [HfX [HcX [Hob Hc]]]]]]]]].
      destruct (instance_of_argument vb ob X HcX Hob) as [E2 HgX]. rewrite E2 in Hc.
      rewrite (unify_type_arguments env K vb _ (instantiate env sigma X) Model.invariant o z [] (gfrag_not_variable env _ (ground_gfrag env _ HgX))) in Hc.
      destruct (ownership_is_assignable_to o _); [|discriminate Hc]. unfold compare_variances in Hc.
      assert (Hgf: forall x, of_fragment env declared x -> (exists K', compare_variances (unify env K') vb Model.invariant X x [] = Some (Ongoing [])) ->
          below env A x).
      { intros x Hx Hcv. apply (Hsnd ob x Hx). intros st' Hl'. rewrite Hl in Hl'. injection Hl' as <-.
        exact (gfits_exact st vb ob X x Ee Hu Hlo HfX Hx Hcv). }
      destruct (below_refl env wf declared declared_wf terminates finite not_expansive X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K (proj2 Hc))).
      + destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; exact EX))) as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K Hc)).
      + destruct (below_bottom env wf declared declared_wf terminates finite not_expansive X HfX) as [kb Eb].
        destruct (subst_below A bottom_type HcA caller_bottom'
            (Hgf bottom_type (bottom_of_fragment env wf declared) ltac:(exists kb; cbn [compare_variances]; exact Eb))) as [f1 E1].
        exact (rtrans _ _ _ HgA ground_bottom Hz (ex_intro _ f1 E1) (ground_takes_bottom z Hz)).
    - (* between bounds: a type of generic code below the upper bound, instantiated *)
      destruct (unify_keeps_exact env (S n) _ A s s' H) as [_ Hk2].
      destruct (proj1 Hs p st Hl) as [_ [_ Hw]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' [He' _]]].
      pose proof (Hfit st' Hl') as Hf. unfold rfits in Hf. rewrite He' in Hf. destruct Hf as [x [Hx [Hcx [Hg ->]]]].
      apply (subst_below A x HcA Hcx). apply (Hsnd o x Hx). intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hg.
Qed.

(* What the variable is assigned to, at run time *)
Lemma rassignee_leaf: forall n p bnd A s s', gwf s -> of_fragment env declared A -> caller A ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
    forall o z, ground env z = true -> (forall st', lookup_state s' p = Some st' -> rfits st' o z) ->
    exists f, unify env f (instantiate env sigma A) z (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p bnd A s s' Hs HA HcA H o z Hz Hfit.
    destruct (gassignee_leaf env wf declared declared_wf terminates finite not_expansive intersect_in_fragment intersect_below
        caller (intersect_generic ps) n p bnd A s s' Hs HA HcA H) as [_ [_ Hsnd]].
    destruct (instance_ground A HcA) as [KA [_ HgA]].
    pose proof (variable_assignee_step env n p bnd A s s' (proj1 HA) H) as H'.
    unfold plus_subtype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (is_exact st) eqn:Ee.
    - destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars env declared A HA) (proj1 (proj1 Hs p st Hl)) H') as [-> _].
      pose proof (Hfit st Hl) as Hf. unfold rfits in Hf. rewrite Ee in Hf.
      destruct Hf as [vb [ob [X [K [Hu [Hlo [HfX [HcX [Hob Hc]]]]]]]]].
      destruct (instance_of_argument vb ob X HcX Hob) as [E2 HgX]. rewrite E2 in Hc.
      rewrite (unify_type_arguments env K vb _ (instantiate env sigma X) Model.invariant o z [] (gfrag_not_variable env _ (ground_gfrag env _ HgX))) in Hc.
      destruct (ownership_is_assignable_to o _); [|discriminate Hc]. unfold compare_variances in Hc.
      assert (Hgf: forall x, of_fragment env declared x -> (exists K', compare_variances (unify env K') vb Model.invariant X x [] = Some (Ongoing [])) ->
          below env x A).
      { intros x Hx Hcv. apply (Hsnd ob x Hx). intros st' Hl'. rewrite Hl in Hl'. injection Hl' as <-.
        exact (gfits_exact st vb ob X x Ee Hu Hlo HfX Hx Hcv). }
      destruct (below_refl env wf declared declared_wf terminates finite not_expansive X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below X A HcX HcA (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ Hz HgX HgA (ex_intro _ K (proj1 Hc)) (ex_intro _ f1 E1)).
      + destruct (below_top env wf declared declared_wf terminates finite not_expansive X HfX) as [kt Et].
        destruct (subst_below top_type A caller_top' HcA
            (Hgf top_type (top_of_fragment env wf declared) ltac:(exists kt; cbn [compare_variances]; exact Et))) as [f1 E1].
        exact (rtrans _ _ _ Hz ground_top HgA (ground_below_top z Hz) (ex_intro _ f1 E1)).
      + destruct (subst_below X A HcX HcA (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; exact EX))) as [f1 E1].
        exact (rtrans _ _ _ Hz HgX HgA (ex_intro _ K Hc) (ex_intro _ f1 E1)).
    - destruct (unify_keeps_exact env (S n) A _ s s' H) as [_ Hk2].
      destruct (proj1 Hs p st Hl) as [_ [_ Hw]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' [He' _]]].
      pose proof (Hfit st' Hl') as Hf. unfold rfits in Hf. rewrite He' in Hf. destruct Hf as [x [Hx [Hcx [Hg ->]]]].
      apply (subst_below x A Hcx HcA). apply (Hsnd o x Hx). intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hg.
Qed.

(* What a nullable type unifies its nested type with, instantiated, is the instance without null *)
Lemma instance_nullable_assignee: forall A, gfrag env A = true -> caller A ->
    without_null env (instantiate env sigma (nullable_assignee env A)) = without_null env (instantiate env sigma A).
Proof.
    intros A HgA HcA.
    destruct (gfrag_cases env A HgA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]]; try reflexivity.
    - cbn [nullable_assignee]. change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
      rewrite without_null_rewrap. reflexivity.
    - destruct HcA as [_ [_ [Hq _]]]. destruct (Hwithin q Hq) as [o [x [Ex [Ho _]]]]. pose proof (Hsf _ o x Ex) as Hx.
      cbn [nullable_assignee]. rewrite without_null_generic.
      destruct (instantiate_exact_generic env sigma (narrow_ref env (mkGenericRef gm nn q bq)) o x Ex Ho (in_fragment_is_gfrag env x Hx)) as [E1 _].
      destruct (instantiate_exact_generic env sigma (mkGenericRef gm nn q bq) o x Ex Ho (in_fragment_is_gfrag env x Hx)) as [E2 _].
      rewrite E1, E2. exact (narrow_ref_inst env _ x Hx).
Qed.

Section Main.

(* The bindings of the callee at run time *)
Variable b: Bindings.
Variable K: nat.
Hypothesis Hb: forall p o z, lookup_binding b p = Some (TypeArgument Model.invariant o z) -> is_exact_ownership o = true /\ ground env z = true.

Let Qa := caller_argument env declared ps.
Let yf := yfrag env declared caller b.
Let ayf := argument_yfrag env declared Qa b.

(* The types of the parameters, instantiated, are ground *)
Lemma instances_ground: forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> bound_in env b K [] (to_generic P) = true -> ground env (inst env b P) = true)
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> bound_in env b K [] (to_generic a) = true ->
        argument_gfrag env (instantiate env b a) = true /\ no_refs (instantiate env b a) = true).
Proof.
    induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (proj2 (Hb p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          ground env (inst env b (RootResolved m c args)) = true).
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP)).
        assert (Hl: length args = length (parameter_ids env c)).
        { destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          - injection Heq as <- <- <-. exact Hl.
          - unfold bottom_type in Heq. injection Heq as _ -> ->. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
        assert (Hargs: forall a, In a args -> argument_gfrag env (instantiate env b a) = true /\ no_refs (instantiate env b a) = true).
        { intros a Ha. destruct (root_parts env wf b K [] m c args HP HbP a Ha) as [Hfa Hba].
          pose proof (vsize_below m c args a Ha). apply IHa; [lia|exact Hfa|exact Hba]. }
        unfold ground. apply andb_true_iff. split.
        - apply make_root_gfrag; [rewrite length_map; exact Hl|].
          intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. exact (proj1 (Hargs a Ha)).
        - change (forallb no_refs (map (instantiate env b) args) = true). apply forallb_forall.
          intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. exact (proj2 (Hargs a Ha)). }
      split.
      + intros P Hd HP HbP. destruct (ifrag_shapes env wf P HP) as [[m [c [args ->]]]|[[m [c [args [-> HP']]]]|[p [bnd ->]]]].
        * exact (Hroot m c args HP HbP Hd).
        * assert (Hb': bound_in env b K [] (to_generic (RootResolved m c args)) = true) by exact HbP.
          simpl in Hd. pose proof (Hroot m c args HP' Hb' ltac:(simpl; lia)) as Hg.
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP')) in Hg.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP')).
          unfold ground in Hg |- *. apply andb_true_iff in Hg. destruct Hg as [Hg Hn].
          change (true && gfrag env (RootResolved m c (map (instantiate env b) args)) && no_refs (RootResolved m c (map (instantiate env b) args)) = true).
          rewrite Hg, Hn. reflexivity.
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (proj2 (Hb p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha HbA; simpl in Ha; try discriminate Ha. simpl in Hd.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [_ Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn). pose proof (IHt n ltac:(lia) Ha Hbn) as Hg.
        unfold ground in Hg. apply andb_true_iff in Hg. exact Hg.
Qed.

Lemma instance_ground_b: forall P, ifrag env P = true -> bound_in env b K [] (to_generic P) = true -> ground env (inst env b P) = true.
Proof. intros P HP Hbp. exact (proj1 (instances_ground (vsize P)) P (le_n _) HP Hbp). Qed.

(* A fold of steps that keep the variable states unify works with, at run time *)
Lemma rfold: forall {X: Type} (h: X -> Unification -> option Unification) (Q: X -> Prop) l s s',
    (forall x, h x Failed = Some Failed) ->
    (forall x, In x l -> forall s0 s0', gwf s0 -> dom b s0 -> h x (Ongoing s0) = Some (Ongoing s0') ->
        gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat b s0' -> Q x)) ->
    gwf s -> dom b s -> fold_unify (fun inner x => h x inner) l (Ongoing s) = Some (Ongoing s') ->
    gwf s' /\ dom b s' /\ (rsat b s' -> rsat b s) /\ keeps_exact s s' /\ (rsat b s' -> forall x, In x l -> Q x).
Proof.
    intros X h Q l. induction l as [|x l IH]; intros s s' Hf Hstep Hs Hd H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [exact Hd|]. split; [auto|]. split; [apply keeps_exact_refl|]. intros _ x [].
    - destruct (h x (Ongoing s)) as [[s1|]|] eqn:E.
      + destruct (Hstep x (or_introl eq_refl) s s1 Hs Hd E) as [Hs1 [Hm1 [Hk1 HQ1]]].
        pose proof (dom_forward b s s1 Hs Hk1 Hd) as Hd1.
        destruct (IH s1 s' Hf (fun x' Hx' => Hstep x' (or_intror Hx')) Hs1 Hd1 H) as [Hs' [Hd' [Hback [Hk' Hall]]]].
        split; [exact Hs'|]. split; [exact Hd'|].
        split; [intros Hr; exact (rsat_back b s s1 Hs Hk1 Hm1 Hd (Hback Hr))|].
        split; [exact (keeps_exact_trans _ _ _ Hk1 Hk')|].
        intros Hr x' [<-|Hx']; [exact (HQ1 (Hback Hr))|exact (Hall Hr x' Hx')].
      + exfalso. clear -H Hf. induction l as [|y l IHl]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHl H).
      + discriminate H.
Qed.

(* The ownership of a type argument of an argument, of the caller, and of a parameter, bound in b *)
Lemma ownership_runtime: forall oa ot, ownership_is_assignable_to oa ot = true -> ownership_free b oa ->
    ownership_bound b ot = true -> ownership_is_assignable_to (instantiate_ownership sigma oa) (instantiate_ownership b ot) = true.
Proof.
    intros oa ot H Hf Hob. destruct ot as [| | |p].
    - destruct oa; try discriminate H. reflexivity.
    - destruct oa; try discriminate H. reflexivity.
    - reflexivity.
    - destruct oa as [| | |q]; try discriminate H. simpl in H. apply param_eqb_eq in H. subst q.
      cbn [ownership_free] in Hf. cbn [ownership_bound] in Hob. rewrite Hf in Hob. discriminate Hob.
Qed.

Lemma ownership_runtime_flipped: forall op oa, ownership_is_assignable_to op oa = true -> ownership_free b oa ->
    ownership_bound b op = true -> ownership_is_assignable_to (instantiate_ownership b op) (instantiate_ownership sigma oa) = true.
Proof.
    intros op oa H Hf Hob. destruct oa as [| | |q].
    - destruct op; try discriminate H. reflexivity.
    - destruct op; try discriminate H. reflexivity.
    - reflexivity.
    - destruct op as [| | |p]; try discriminate H. simpl in H. apply param_eqb_eq in H. subst p.
      cbn [ownership_free] in Hf. cbn [ownership_bound] in Hob. rewrite Hf in Hob. discriminate Hob.
Qed.

Let gen := generic_arguments env wf declared declared_wf terminates finite not_expansive intersect_in_fragment supertype_in_fragment
    intersect_below supertype_above caller Qa (caller_argument_nested env declared ps) (intersect_generic ps) (supertype_generic ps)
    caller_top' caller_bottom' (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
    (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b K.

Lemma yf_top: yf top_type.
Proof. exact (yfrag_top env wf declared caller caller_top' b). Qed.

Lemma yf_bottom: yf bottom_type.
Proof. exact (yfrag_bottom env wf declared caller caller_bottom' b). Qed.

Lemma instance_top: instantiate env sigma top_type = top_type.
Proof. reflexivity. Qed.

Lemma instance_bottom: instantiate env sigma bottom_type = bottom_type.
Proof. reflexivity. Qed.

(*
 * Inference is sound at run time: what unify accepts of an argument of generic code for a parameter,
 * the argument instantiated takes, with the type variables replaced by what they stand for at run
 * time (rsat): the type arguments, instantiated, of those bound exactly, and the instances of types of
 * generic code between their bounds.
 *)
Lemma runtime_arguments: forall n,
    (forall P A s s', ifrag env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', ifrag env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env sigma A) (inst env b P) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', argument_ifrag env P = true -> ayf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', argument_ifrag env P = true -> ayf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env sigma A) (instantiate env b P) (Ongoing []) = Some (Ongoing [])).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    destruct (gen n) as [Gt [Ga [Gat Gaa]]].
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', gwf s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat b s0' -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        gwf s -> dom b s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        rsat b s' ->
        exists f, fold_unify (fun inner '(t, a) => unify env f t a inner) (combine (map inst_t targs) (map inst_a aargs)) (Ongoing [])
            = Some (Ongoing [])).
    { intros targs aargs s s' inst_t inst_a Hp Hs Hd H Hr.
      destruct (rfold (fun x inner => let '(t, a) := x in unify env n t a inner)
          (fun x => let '(t, a) := x in exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))
          (combine targs aargs) s s') as [_ [_ [_ [_ Hall]]]].
      - intros [t a]. apply unify_keeps_failure.
      - intros [t a] Hin s0 s0' Hs0 Hd0 E. exact (Hp t a Hin s0 s0' Hs0 Hd0 E).
      - exact Hs.
      - exact Hd.
      - exact H.
      - destruct (uniform_fuel (combine targs aargs) (fun f '(t, a) => unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing [])))
            as [f Hf].
        + intros f f' [t a] Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E).
        + intros [t a] Hin. exact (Hall Hr (t, a) Hin).
        + exists f. apply fold_from_pairs. intros x y Hin. destruct (combine_map_in inst_t inst_a _ _ x y Hin) as [t [a [Hin' [-> ->]]]].
          exact (Hf (t, a) Hin'). }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A s s' HP HA Hbp Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          yf (RootResolved ma ca aargs) -> caller (RootResolved ma ca aargs) ->
          bound_in env sigma KA [] (RootResolved ma ca aargs) = true ->
          bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (inst env b (RootResolved mt ct targs)) (instantiate env sigma (RootResolved ma ca aargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros mt ct targs ma ca aargs Hft Hfa Hca Hba Hbt Hu.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft)), instantiate_class.
        pose proof (root_parts env wf b K [] mt ct targs Hft Hbt) as Htargs.
        destruct (yfrag_root env declared caller Qa (caller_root env declared ps) b ma ca aargs Hfa) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { exists 1. rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs),
              (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn. reflexivity. }
        assert (Haw: forall a, In a aargs -> argument_wfrag env a = true /\ bound_in env sigma KA [] a = true).
        { intros a Ha. split; [exact (wtfrag_root_arguments env ma ca aargs a (proj1 Hca) Ha)|exact (bound_in_root env sigma KA [] ma ca aargs Hba a Ha)]. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm: (forall a, In a norm -> ayf a)
            /\ (if class_eqb ca ct then map (instantiate env sigma) aargs
                else parameterized_supertype_arguments env ca (map (instantiate env sigma) aargs) ct) = map (instantiate env sigma) norm).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne].
          - rewrite class_eqb_refl. split; [|reflexivity]. intros a Ha. exact (Haargs a Ha).
          - rewrite (class_eqb_false _ _ Hne). pose proof (class_eqb_false_neq _ _ Hcn) as Hcn'.
            destruct (wide_supertype_arguments_commute env wf sigma KA Hsf ca ct aargs Hne Hcn' Hbase Hla Haw) as [Hcomm _].
            split; [|exact Hcomm]. intros a Ha.
            pose proof (proj2 (supertype_arguments_yfrag env wf declared Qa (caller_supertype_arguments env wf declared ps) b ca ct aargs
                Hne Hcn' Hbase Hla Haargs) a Ha) as Hya.
            exact Hya. }
        destruct Hnorm as [Hnorm Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', gwf s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat b s0' -> exists f, unify env f (instantiate env b t) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 Hd0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Htargs t Ht) as [Hft' Hbt']. pose proof (Hnorm a Ha) as Hya.
          destruct (Gat t a s0 s0' Hft' Hya Hbt' Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. exact (IHat t a s0 s0' Hft' Hya Hbt' Hs0 Hd0 E Hr0). }
        destruct (Hpairs targs norm s s' (instantiate env b) (instantiate env sigma) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes env wf P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA HcA HbA Hbp H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          pose proof (yfrag_generic env wf declared declared_wf caller (caller_bound env wf declared ps) b _ HA) as Hyb.
          destruct (IHt _ _ s s' HP Hyb Hbp Hs Hd H Hr) as [f1 E1].
          set (g := mkGenericRef gm nn q bq) in *.
          destruct (binds_ref_some env wf sigma KA [] g HbA) as [o [x [Ex [Ho [Hgx [Hresp Hbbq]]]]]].
          set (bd := effective_bound env g) in *.
          destruct (instance_ground bd (proj2 (proj2 (proj2 Hyb)))) as [Kb [_ Hgb]].
          destruct (instantiate_exact_generic env sigma g o x Ex Ho Hgx) as [EA _].
          rewrite (inst_nested_instantiate env wf sigma KA [] bd (proj1 (generic_of_wtfrag env wf _ (proj1 HcA))) Hbbq) in Hresp.
          rewrite EA in HgA |- *. unfold respects in Hresp.
          destruct (unify env KA (instantiate env sigma bd) (inst_ref env g x) (Ongoing [])) as [[w|]|] eqn:Ew;
              try discriminate Hresp.
          rewrite (ground_keeps env wf KA _ _ [] w Hgb HgA Ew) in Ew.
          exact (rtrans _ _ _ HgA Hgb (instance_ground_b _ HP Hbp) (ex_intro _ KA Ew) (ex_intro _ f1 E1)).
        * (* an intersection: through the component taken *)
          rewrite step_root_inter in H. destruct (flipped_some env n _ cs s s' H) as [c [Hc Ec]].
          destruct (yfrag_component env declared caller (caller_component env declared ps) b cs c HA Hc) as [Hyc _].
          destruct (IHt _ _ s s' HP Hyc Hbp Hs Hd Ec Hr) as [f1 E1].
          pose proof (proj2 (proj2 (proj2 Hyc))) as Hcc. destruct (instance_ground c Hcc) as [Kc [_ Hgc]].
          destruct (subst_below _ c HcA Hcc (intersection_below_component env wf declared declared_wf terminates finite
              not_expansive cs c (proj1 HA) Hc)) as [f2 E2].
          exact (rtrans _ _ _ HgA Hgc (instance_ground_b _ HP Hbp) (ex_intro _ f2 E2) (ex_intro _ f1 E1)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hbp.
        pose proof (yfrag_nullable_assignee env wf declared declared_wf caller (caller_nullable env declared ps)
            (caller_narrowed env wf declared ps) b A HA) as HyN.
        destruct (IHt _ _ s s' HP' HyN Hb' Hs Hd H Hr) as [f1 E1].
        pose proof (instance_ground_b _ HP' Hb') as HgP.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in E1, HgP.
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP')).
        destruct (instance_ground _ (proj2 (proj2 (proj2 HyN)))) as [KN [_ HgN]].
        pose proof (ground_non_null env f1 _ _ [] [] HgP HgN eq_refl E1) as HnN.
        exists (S f1). rewrite (ground_nullable_target env f1 _ _ [] HgA).
        rewrite <- (instance_nullable_assignee A (proj1 (proj1 HA)) HcA), (ground_non_null_without_null env _ HgN HnN).
        exact E1.
      + (* a type variable *)
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hbp) as [o [z [Ez _]]]. cbn [param_of] in Ez.
        destruct (Hr p o z Ez) as [st' [Hl' Hf']].
        rewrite (inst_variable env b p bnd _ _ _ Ez).
        apply (rtarget_leaf n p bnd A s s' Hs (proj1 HA) (proj1 (proj2 HA)) HcA H o z (proj2 (Hb p o z Ez))).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
    - (* a type with type variables as the assignee *)
      intros P A s s' HP HA Hbp Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          yf (RootResolved ma ca aargs) ->
          bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (instantiate env sigma (RootResolved ma ca aargs)) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hbp' Hu.
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp)), instantiate_class.
        pose proof (root_parts env wf b K [] mp cp pargs Hfp Hbp') as Hpargs.
        destruct (yfrag_root env declared caller Qa (caller_root env declared ps) b ma ca aargs Hfa) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { exists 1. rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs),
              (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hnorm': (forall a, In a norm -> argument_ifrag env a = true /\ bound_in env b K [] (to_generic a) = true)
            /\ (if class_eqb cp ca then map (instantiate env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate env b) pargs) ca) = map (instantiate env b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables env wf b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', gwf s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat b s0' -> exists f, unify env f (instantiate env sigma t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 Hd0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. pose proof (Haargs t Ht) as Hyt.
          destruct (Gaa a t s0 s0' Hfa' Hyt Hba' Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. exact (IHaa a t s0 s0' Hfa' Hyt Hba' Hs0 Hd0 E Hr0). }
        destruct (Hpairs aargs norm s s' (instantiate env sigma) (instantiate env b) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes env wf P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + pose proof (instance_ground_b _ HP Hbp) as HgP.
        destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA Hbp H).
        * rewrite unify_nullable_class in H.
          pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Hyn.
          destruct (IHa _ _ s s' HP Hyn Hbp Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in E1, HgP |- *.
          rewrite unify_nullable_class. exact (ground_unify_without_null env f1 _ _ [] [] HgN HgP E1).
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          injection H as <-. apply andb_true_iff in Ec. destruct Ec as [Ec _]. cbn [is_non_nullable_nothing] in Ec.
          destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [Hcn _]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          -- injection Heq as <- <- <-. rewrite Ec in Hcn. discriminate Hcn.
          -- rewrite Heq. exact (ground_takes_bottom _ HgA).
        * (* an intersection: each of its components takes it *)
          rewrite unify_step_once in H. unfold unify_step, unify_intersection in H.
          destruct (no_vars_filter cs (gfrag_components_no_vars env cs (proj1 (proj1 HA)))) as [Hvar Hnonvar].
          rewrite Hvar, Hnonvar in H. cbn zeta in H.
          set (Pc := RootResolved mp cp pargs) in *.
          destruct (fold_unify (fun inner component => unify env n component Pc inner) cs (Ongoing s)) as [[s2|]|] eqn:E1; try discriminate H.
          assert (Hstep: forall c, In c cs -> forall s0 s0', gwf s0 -> dom b s0 -> unify env n c Pc (Ongoing s0) = Some (Ongoing s0') ->
              gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
              /\ (rsat b s0' -> exists f, unify env f (instantiate env sigma c) (inst env b Pc) (Ongoing []) = Some (Ongoing []))).
          { intros c Hc s0 s0' Hs0 Hd0 E. destruct (yfrag_component env declared caller (caller_component env declared ps) b cs c HA Hc) as [Hyc _].
            destruct (Ga Pc c s0 s0' HP Hyc Hbp Hs0 E) as [Hs0' [Hm0 _]].
            split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n c Pc s0 s0' E)|].
            intros Hr0. exact (IHa Pc c s0 s0' HP Hyc Hbp Hs0 Hd0 E Hr0). }
          destruct (rfold (fun c inner => unify env n c Pc inner)
              (fun c => exists f, unify env f (instantiate env sigma c) (inst env b Pc) (Ongoing []) = Some (Ongoing []))
              cs s s2 (fun c => unify_keeps_failure env n c Pc) Hstep Hs Hd E1) as [Hs2 [Hd2 [_ [_ Hall]]]].
          assert (Hr2: rsat b s2).
          { destruct (find_first (fun component => unify env n component Pc (Ongoing s2)) cs) as [[[cov s3]|]|] eqn:E2; try discriminate H.
            - cbn in H. injection H as <-. destruct (find_first_found _ _ _ _ E2) as [Hin E3].
              destruct (Hstep cov Hin s2 s3 Hs2 Hd2 E3) as [_ [Hm3 [Hk3 _]]].
              exact (rsat_back b s2 s3 Hs2 Hk3 Hm3 Hd2 Hr).
            - cbn in H. injection H as <-. exact Hr. }
          pose proof (Hall Hr2) as Hcs.
          destruct (inst_intersection env wf sigma KA Hsf cs (proj1 HcA) HbA) as [EI Hci].
          rewrite EI in HgA |- *.
          apply (ground_accepts env wf declared declared_wf terminates finite not_expansive _ _ HgA HgP).
          destruct (wcomponents_facts env cs (proj1 HcA)) as [_ Hcomp].
          apply (inter_target_never_fails env wf); [ |exact (ground_no_vars env _ HgP)|exact I| ].
          { apply forallb_forall. intros y Hy. apply (ground_no_vars env).
            apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
            destruct (Hci c Hin) as [Hgc Hcl]. exact (proj1 (ground_with_mutability env _ _ Hcl Hgc)). }
          intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
          destruct (Hci c Hin) as [Hgc Hcl]. destruct (Hcs c Hin) as [f Ef].
          apply (with_mutability_target_never_fails env wf f _ _ _ Hgc Hcl HgP Ef).
          intros c' Hc'. cbn [intersected_components] in Hc'. destruct Hc' as [<-|[]].
          unfold common_mutability. apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|].
          intros k Hk. apply in_map_iff in Hk. destruct Hk as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c2 [<- Hin2]].
          destruct (Hcs c2 Hin2) as [f2 Ef2]. destruct (Hci c2 Hin2) as [Hgc2 _].
          exact (ground_mutability env wf f2 _ _ [] [] Hgc2 HgP Ef2).
      + pose proof (instance_ground_b _ HP Hbp) as HgP.
        destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * rewrite unify_class_nullable in H. discriminate H.
        * rewrite unify_nullable_nullable in H.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hbp.
          pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Hyn.
          destruct (IHa _ _ s s' HP' Hyn Hb' Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          pose proof (instance_ground_b _ HP' Hb') as HgPn.
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP')) in E1, HgPn.
          rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP')), unify_nullable_nullable.
          exact (ground_unify_without_null env f1 _ _ [] [] HgN HgPn E1).
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H. discriminate H.
      + (* a type variable *)
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hbp) as [o [z [Ez _]]]. cbn [param_of] in Ez.
        destruct (Hr p o z Ez) as [st' [Hl' Hf']].
        rewrite (inst_variable env b p bnd _ _ _ Ez).
        apply (rassignee_leaf n p bnd A s s' Hs (proj1 HA) HcA H o z (proj2 (Hb p o z Ez))).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA Hbp Hs Hd H Hr; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      destruct (proj2 (proj2 (proj2 (proj2 HA)))) as [HcN [Hmq _]].
      destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hbp) as [Hob Hbn].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na
          (not_capturable env (of_fragment env declared) (of_fragment env declared) s nt (proj1 Hs))) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      destruct (instance_of_argument va oa na HcN Hmq) as [EA HgN].
      pose proof (ownership_runtime oa ot Ho Hoa Hob) as Hown.
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (ifrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) (instantiate env sigma na) [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (instantiate env sigma (TypeArgument va oa na)) (Ongoing [])
              = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn), EA.
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va _ (instantiate env sigma na) [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (Gt nt na s s1 HP HAn Hbn Hs E1) as [Hs1 [_ _]].
           pose proof (unify_keeps_exact env n nt na s s1 E1) as Hk1. pose proof (dom_forward b s s1 Hs Hk1 Hd) as Hd1.
           destruct (Ga nt na s1 s' HP HAn Hbn Hs1 H) as [_ [Hm2 _]]. pose proof (unify_keeps_exact env n na nt s1 s' H) as Hk2.
           destruct (IHa nt na s1 s' HP HAn Hbn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHt nt na s s1 HP HAn Hbn Hs Hd E1 (rsat_back b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HAn Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHa nt na s s' HP HAn Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHt nt top_type s s' HP yf_top Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHa nt bottom_type s s' HP yf_bottom Hbn Hs Hd H Hr) as [f Hf] ];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA Hbp Hs Hd H Hr; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      destruct (proj2 (proj2 (proj2 (proj2 HA)))) as [HcN [Hmq _]].
      destruct (bound_in_argument env b K [] vp op (to_generic np) Hbp) as [Hop Hbn].
      rewrite (unify_type_arguments env n va oa na vp op np s (gfrag_not_variable env na (proj1 (proj1 HAn)))) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      destruct (instance_of_argument va oa na HcN Hmq) as [EA HgN].
      pose proof (ownership_runtime_flipped op oa Ho Hoa Hop) as Hown.
      assert (Hgoal: forall f, compare_variances (unify env f) va vp (instantiate env sigma na) (inst env b np) [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env sigma (TypeArgument va oa na)) (instantiate env b (TypeArgument vp op np)) (Ongoing [])
              = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vp op np HP Hbn), EA.
        rewrite (unify_type_arguments env f va _ (instantiate env sigma na) vp _ (inst env b np) [] (gfrag_not_variable env _ (ground_gfrag env _ HgN))), Hown.
        exact E. }
      pose proof (of_fragment_no_vars env declared na (proj1 HAn)) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (Ga np na s s1 HP HAn Hbn Hs E1) as [Hs1 [_ _]].
           pose proof (unify_keeps_exact env n na np s s1 E1) as Hk1. pose proof (dom_forward b s s1 Hs Hk1 Hd) as Hd1.
           destruct (Gt np na s1 s' HP HAn Hbn Hs1 H) as [_ [Hm2 _]]. pose proof (unify_keeps_exact env n np na s1 s' H) as Hk2.
           destruct (IHt np na s1 s' HP HAn Hbn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHa np na s s1 HP HAn Hbn Hs Hd E1 (rsat_back b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HAn Hbn Hs Hd H Hr) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HAn Hbn Hs Hd H Hr) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | (* no type variables involved: Nothing and read Any? *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free env wf k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0]
            end ].
      + (* in against out: na takes Nothing only *)
        destruct (subst_below na bottom_type HcN caller_bottom' (ex_intro _ n H0)) as [f Hf].
        exists (S f). apply Hgoal. unfold compare_variances. rewrite instance_bottom in Hf. exact Hf.
      + (* out against in: what na reads as, read Any?, is below it *)
        destruct (subst_below top_type na caller_top' HcN (ex_intro _ n H0)) as [f Hf].
        exists (S f). apply Hgoal. unfold compare_variances. rewrite instance_top in Hf. exact Hf.
Qed.

End Main.

(* ---------------------------------------------------------------------------------------------- *)
(* Capturing the type arguments of a receiver of generic code                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gcapture_step: forall n p bound s y u,
    lookup_state s p = Some (mkVariableState bound bound bottom_type false true) ->
    argument_gfrag env y = true ->
    unify env n (receiver_leaf (p, bound)) y (Ongoing s) = Some (Ongoing u) ->
    u = set_state s p (mkVariableState bound y y true true).
Proof.
    intros n p bound s [| | | |vy oy Y| |] u Hl Hy H; simpl in Hy; try discriminate Hy.
    destruct n as [|n]; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_type_argument, receiver_leaf in H. cbn beta iota zeta in H.
    replace (ownership_is_assignable_to oy any_ownership) with true in H by (destruct oy; reflexivity).
    cbn [negb fst snd] in H. unfold capturable in H. cbn beta iota in H. rewrite Hl in H. cbn [is_capturable is_exact negb andb] in H.
    unfold plus_exact_binding in H. rewrite Hl in H. cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    destruct (unify env n bound Y (Ongoing s)) as [[w|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument vy oy Y) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    injection H as <-. f_equal.
    destruct n as [|n]; [discriminate E2|].
    destruct vy; rewrite unify_step_once in E2; unfold unify_step, unify_type_argument in E2; cbn beta iota zeta in E2;
        try (injection E2 as <-; reflexivity).
    - exact (gkeeps env wf n Y bottom_type s w' Hy (bottom_gfrag env wf) E2).
    - exact (gkeeps env wf n Y bottom_type s w' Hy (bottom_gfrag env wf) E2).
Qed.

Lemma gcapture_arguments: forall n vars ys s u,
    NoDup (map fst vars) -> length ys = length vars ->
    (forall y, In y ys -> argument_gfrag env y = true) ->
    (forall p bound, In (p, bound) vars -> lookup_state s p = Some (mkVariableState bound bound bottom_type false true)) ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine (map receiver_leaf vars) ys) (Ongoing s) = Some (Ongoing u) ->
    (forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true))
    /\ (forall q, ~ In q (map fst vars) -> lookup_state u q = lookup_state s q).
Proof.
    intros n vars. induction vars as [|[p bound] rest IH]; intros [|y ys] s u Hnd Hl Hys Hvars H; simpl in Hl; try discriminate Hl.
    - simpl in H. injection H as <-. split; [intros [|i]; discriminate|reflexivity].
    - inversion Hnd as [|? ? Hnotin Hnd']. subst.
      simpl in H. destruct (unify env n (receiver_leaf (p, bound)) y (Ongoing s)) as [[s1|]|] eqn:E;
          [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      pose proof (gcapture_step n p bound s y s1 (Hvars p bound (or_introl eq_refl)) (Hys y (or_introl eq_refl)) E) as ->.
      destruct (IH ys (set_state s p (mkVariableState bound y y true true)) u Hnd' ltac:(lia) (fun y' Hy' => Hys y' (or_intror Hy')))
          as [IH1 IH2]; [|exact H|].
      + intros q bq Hin. rewrite lookup_set_other; [exact (Hvars q bq (or_intror Hin))|]. intros ->. apply Hnotin. exact (in_map fst _ _ Hin).
      + split.
        * intros [|i] q bq y' Hq Hy'.
          -- simpl in Hq, Hy'. injection Hq as <- <-. injection Hy' as <-. rewrite (IH2 p Hnotin). apply lookup_set_same.
          -- exact (IH1 i q bq y' Hq Hy').
        * intros q Hq. simpl in Hq. rewrite (IH2 q (fun H' => Hq (or_intror H'))). apply lookup_set_other.
          intros ->. apply Hq. left. reflexivity.
Qed.

Lemma no_refs_not_loose: forall t, no_refs t = true -> mentions_loosely_bound sigma t = false /\ mentions_loosely_bound_in_arguments sigma t = false.
Proof.
    intros t. remember (esize t) as e eqn:He. revert t He. induction e as [e IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|g|me msg|v o n|g|cs]; cbn [no_refs] in H; try discriminate H.
    - assert (Ha: existsb (mentions_loosely_bound sigma) args = false).
      { apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Ha Ea]]. rewrite forallb_forall in H.
        rewrite (proj1 (IH (esize a) ltac:(pose proof (esize_in args a Ha); simpl; lia) a eq_refl (H a Ha))) in Ea. discriminate Ea. }
      split; exact Ha.
    - exact (IH (esize n) ltac:(simpl; lia) n eq_refl H).
    - split; [exact (proj1 (IH (esize n) ltac:(simpl; lia) n eq_refl H))|reflexivity].
    - assert (Hc: forall a, In a cs -> mentions_loosely_bound sigma a = false /\ mentions_loosely_bound_in_arguments sigma a = false).
      { intros a Ha. rewrite forallb_forall in H. exact (IH (esize a) ltac:(pose proof (esize_in cs a Ha); simpl; lia) a eq_refl (H a Ha)). }
      split; apply not_true_iff_false; intros E; apply existsb_exists in E; destruct E as [a [Ha Ea]].
      + change (mentions_loosely_bound sigma a = true) in Ea. rewrite (proj1 (Hc a Ha)) in Ea. discriminate Ea.
      + change (mentions_loosely_bound_in_arguments sigma a = true) in Ea. rewrite (proj2 (Hc a Ha)) in Ea. discriminate Ea.
Qed.

(* Class types without type parameters stay as they are *)
Lemma instantiate_class_types: forall k t, depth t <= k -> in_fragment env t = true -> closed t = true -> instantiate env sigma t = t.
Proof.
    induction k as [|k IH].
    { intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; simpl in Hd; lia. }
    assert (Hroot: forall m c args, depth (RootResolved m c args) <= S k -> in_fragment env (RootResolved m c args) = true ->
        closed (RootResolved m c args) = true -> instantiate env sigma (RootResolved m c args) = RootResolved m c args).
    { intros m c args Hd Ht Hc. rewrite instantiate_class. f_equal. transitivity (map (fun a => a) args); [|apply map_id].
      apply map_ext_in. intros a Ha. pose proof (proj2 (root_in_fragment env m c args Ht) a Ha) as Hfa.
      destruct a as [| | | |v o n| |]; try discriminate Hfa. cbn [argument_in_fragment] in Hfa.
      destruct (closed_argument v o n (closed_parts m c args Hc _ Ha)) as [Ho Hcn].
      pose proof (argument_depth_below m c args _ Ha). cbn [argument_depth] in *.
      pose proof (IH n ltac:(lia) Hfa Hcn) as En.
      pose proof (proj2 (in_fragment_no_refs env (S (depth n))) (TypeArgument v o n) (le_n _) Hfa) as Hnr. cbn [no_refs] in Hnr.
      rewrite (instantiate_argument_plain env sigma v o n n En (proj2 (no_refs_not_loose n Hnr))).
      - destruct o; try discriminate Ho; reflexivity.
      - destruct (fragment_cases env n Hfa) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; reflexivity. }
    intros t Hd Ht Hc. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> Ht']]]]].
    - exact (Hroot m c args Hd Ht Hc).
    - rewrite depth_nullable in Hd. change (rewrap_nullable (instantiate env sigma (RootResolved m c args)) = Nullable (RootResolved m c args)).
      rewrite (Hroot m c args ltac:(lia) Ht' Hc). reflexivity.
Qed.

Let ginv := generic_invocation_sound env wf declared declared_wf terminates finite not_expansive intersect_in_fragment
    supertype_in_fragment intersect_below supertype_above caller (caller_argument env declared ps) (caller_argument_nested env declared ps)
    (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom' (caller_root env declared ps) (caller_nullable env declared ps)
    (caller_bound env wf declared ps) (caller_narrowed env wf declared ps) (caller_component env declared ps)
    (caller_supertype_arguments env wf declared ps).

(*
 * Calling a member function on a receiver of generic code is sound at run time: the receiver's type
 * mentions the type parameters of the caller (`list.add(x)` with `list: List<T>`); unifying the
 * receiver parameter captures its type arguments, which, instantiated, the type arguments of the
 * object at run time are within. Whatever argument of generic code inference accepts for a parameter,
 * instantiated, fits the parameter with the type parameters of c replaced by the type arguments of
 * the object as c, and those of the function by their final values, instantiated.
 *)
Theorem member_call_on_generic_receiver: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (forall p bound, In (p, bound) ovars -> caller bound /\ closed bound = true) ->
    (* the receiver, of generic code, unified with the receiver parameter *)
    of_fragment env declared (RootResolved ma ca ys) -> caller (RootResolved ma ca ys) ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is at run time, below the receiver instantiated; its type arguments exact, and as
       those of c within the bounds *)
    in_fragment env (RootResolved mo e xs) = true -> nothing_is_bottom (RootResolved mo e xs) = true ->
    closed (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (instantiate env sigma (RootResolved ma ca ys)) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, and the arguments of generic code, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ owners_outside env (map fst (cvars ++ ovars)) A
        /\ caller A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs
        ++ map (fun v => (fst v, TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U (fst v))))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f (instantiate env sigma A) (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds HQbounds HfR HcR Hrec
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HAs Hfold b Hbdef P A HPA.
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) (map fst cvars)))) vars).
    assert (Hs0: for_inference_of vars (map fst cvars) = Ongoing s0) by reflexivity.
    rewrite Hs0 in Hrec.
    assert (Hndc: NoDup (map fst cvars)) by exact (nodup_app_l _ _ Hnd).
    assert (Hcls: forall p bound, In (p, bound) cvars -> existsb (param_eqb p) (map fst cvars) = true).
    { intros p bound Hin. apply existsb_exists. exists p. split; [exact (in_map fst _ _ Hin)|apply param_eqb_refl]. }
    assert (Hown: forall p bound, In (p, bound) ovars -> existsb (param_eqb p) (map fst cvars) = false).
    { intros p bound Hin. apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [q [Hq Hpq]].
      apply param_eqb_eq in Hpq. subst q. exact (nodup_app_disjoint _ _ p Hnd Hq (in_map fst _ _ Hin)). }
    (* the receiver, as a reference to c, binds the type parameters of c exactly *)
    destruct n as [|n]; [discriminate Hrec|].
    rewrite unify_classes in Hrec.
    destruct (base_type_is_subtype_of env ca c) eqn:Hbca; [|discriminate Hrec].
    destruct (Model.is_subtype_of _ _) eqn:Hmr; [|discriminate Hrec].
    rewrite (class_eqb_false ca nothing Hca) in Hrec. unfold unify_arguments in Hrec.
    set (ys' := if class_eqb ca c then ys else parameterized_supertype_arguments env ca ys c) in Hrec.
    destruct (root_gfrag env ma ca ys (proj1 HfR)) as [Hly0 Hgys].
    assert (Hcys: forall y, In y ys -> caller_argument env declared ps y) by (intros y Hy; exact (caller_root env declared ps ma ca ys y HcR Hy)).
    assert (Hsys: forall y, In y ys -> is_type_argument y = true)
        by (intros y Hy; exact (argument_gfrag_type_argument env y (Hgys y Hy))).
    destruct (instance_ground _ HcR) as [KR [HbR HgR]].
    assert (Hysr: forall y, In y ys -> argument_wfrag env y = true /\ bound_in env sigma KR [] y = true).
    { intros y Hy. split; [exact (wtfrag_root_arguments env ma ca ys y (proj1 HcR) Hy)|exact (bound_in_root env sigma KR [] ma ca ys HbR y Hy)]. }
    (* the type arguments of the receiver, as those of c: of generic code, and instantiated *)
    assert (Hys': length ys' = length (parameter_ids env c) /\ (forall y, In y ys' ->
        argument_gfrag env y = true /\ refs_wf env declared y /\ caller_argument env declared ps y
        /\ argument_wfrag env y = true /\ bound_in env sigma KR [] y = true)
        /\ (if class_eqb ca c then map (instantiate env sigma) ys
            else parameterized_supertype_arguments env ca (map (instantiate env sigma) ys) c) = map (instantiate env sigma) ys').
    { unfold ys'. destruct (Class_eq_dec ca c) as [<-|Hne].
      - rewrite class_eqb_refl. split; [exact Hly0|]. split; [|reflexivity]. intros y Hy. split; [exact (Hgys y Hy)|].
        split; [exact I|]. split; [exact (Hcys y Hy)|].
        destruct (Hysr y Hy) as [H3 H4]. auto.
      - rewrite (class_eqb_false _ _ Hne).
        assert (Hta: forall y, In y ys -> is_type_argument y = true) by (intros y Hy; exact (Hsys y Hy)).
        destruct (supertype_arguments_gfrag env wf ca c ys Hne Hca Hbca Hly0 Hgys) as [Hl' Hg'].
        destruct (wide_supertype_arguments_commute env wf sigma KR Hsf ca c ys Hne Hca Hbca Hly0 Hysr) as [Hcomm Hwb].
        split; [exact Hl'|]. split; [|exact Hcomm]. intros y Hy. split; [exact (Hg' y Hy)|].
        split; [exact I|].
        split; [exact (caller_supertype_arguments env wf declared ps ca c ys Hne Hca Hbca Hly0 Hcys y Hy)|].
        destruct (Hwb y Hy) as [H3 H4]. auto. }
    destruct Hys' as [Hly [Hys Hcomm]].
    assert (Hl: length ys' = length cvars) by (rewrite Hly, <- Hids, length_map; reflexivity).
    assert (Hfresh: forall p bound, In (p, bound) cvars -> lookup_state s0 p = Some (mkVariableState bound bound bottom_type false true)).
    { intros p bound Hin. unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin).
      reflexivity. }
    destruct (gcapture_arguments n cvars ys' s0 u Hndc Hl (fun y Hy => proj1 (Hys y Hy)) Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound bound bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variable states unify works with *)
    assert (Hu: forall p st, lookup_state u p = Some st ->
        (exists i bound y, nth_error cvars i = Some (p, bound) /\ nth_error ys' i = Some y /\ st = mkVariableState bound y y true true)
        \/ (exists bound, In (p, bound) ovars /\ st = mkVariableState bound bound bottom_type false false)).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
      - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        rewrite (Hcap i p bound y Hi Hy) in Hp. injection Hp as <-. left. exists i, bound, y. auto.
      - pose proof Hp as Hp2. rewrite (Hoth p Hnin) in Hp2. unfold s0 in Hp2. destruct (lookup_for_inference_in _ _ p st Hp2) as [bound Hin].
        apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
        right. exists bound. split; [exact Hin|]. rewrite (Hownu p bound Hin) in Hp. injection Hp as <-. reflexivity. }
    assert (Hwfu: gwf u).
    { split.
      - intros p st Hp. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]]; cbn [upper_bound lower_bound is_exact is_capturable].
        + pose proof (argument_gfrag_no_vars env y (proj1 (Hys y (nth_error_In _ _ Hy)))) as Hny.
          split; [exact Hny|]. split; [exact Hny|]. intros E; discriminate E.
        + pose proof (Hbounds p bound (in_or_app _ _ _ (or_intror Hin))) as Hfb.
          split; [exact (of_fragment_no_vars env declared bound (of_fragment_of_class env declared bound Hfb))|]. split; [reflexivity|].
          intros _. split; [reflexivity|]. split; [exists 2; apply (below_all env wf [] bound 2 Hfb); lia|].
          split; [intros x f _ Ex; exists f; exact Ex|].
          split; [exact (of_fragment_of_class env declared bound Hfb)|exact (bottom_of_fragment env wf declared)].
      - intros p st Hp He'. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]]; [discriminate He'|].
        cbn [upper_bound lower_bound]. split; [exact (proj1 (HQbounds p bound Hin))|exact caller_bottom']. }
    (* the generic inference: its variable states, and the final values *)
    assert (HAs': forall b', (forall q, ~ In q (map fst vars) -> lookup_binding b' q = None) -> forall A, In A As -> yfrag env declared caller b' A).
    { intros b' Hb' A' HA'. destruct (HAs A' HA') as [Hf [Hbo [Ho Hq]]]. split; [exact Hf|]. split; [exact Hbo|].
      split; [exact (owners_outside_free env wf _ b' Hb' A' Ho)|exact Hq]. }
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (uniform_fuel_list vars (fun f v => unify env f (snd v) (snd v) (Ongoing []) = Some (Ongoing []))) as [K0 HK0].
    { intros f f' v Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { intros [p bound] Hin. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (to_generic P) = true).
    { intros P' HP'. apply (bound_in_from_refs env wf vars _ _ P' (or_introl (proj1 (HPs P' HP'))) (proj2 (HPs P' HP'))).
      - intros p bound Hin. unfold binds_exactly, b0. rewrite (lookup_map_vars vars _ p bound Hnd' Hin). cbn [snd].
        rewrite (in_fragment_is_gfrag env _ (Hbounds p bound Hin)). unfold respects. pose proof (HK0 (p, bound) Hin) as E0.
        cbn [snd] in E0. rewrite E0. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (ginv nf Ps As u U b0 K0 Hwfu (fun P' HP' => conj (proj1 (HPs P' HP')) (Hb0 P' HP'))
        (HAs' b0 (fun q Hq => lookup_map_none vars _ q Hq)) Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep Hkeep2].
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ final_value_of env U p = Constraints.final_value env st /\ of_fragment env declared (final_value_of env U p)
        /\ caller (final_value_of env U p) /\ gfits env declared st ref (final_value_of env U p)
        /\ exists f, unify env f bound (final_value_of env U p) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      destruct (proj1 HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [Hbs [Hbu Hbl]]]].
      destruct (proj2 HwfU p st2 HlU He2) as [Hqu Hql].
      assert (Ef: final_value_of env U p = Constraints.final_value env st2) by (unfold final_value_of; rewrite HlU; reflexivity).
      assert (Hff: of_fragment env declared (Constraints.final_value env st2))
          by (unfold Constraints.final_value; destruct (is_non_nullable_nothing env (lower_bound st2)); assumption).
      assert (Hqf: caller (Constraints.final_value env st2))
          by (unfold Constraints.final_value; destruct (is_non_nullable_nothing env (lower_bound st2)); assumption).
      pose proof (generic_final_value_fits env wf declared declared_wf terminates finite not_expansive caller U p st2 ref HwfU HlU He2 Hff) as Hfit.
      exists st2. rewrite Ef. split; [exact HlU|]. split; [exact He2|]. split; [reflexivity|]. split; [exact Hff|]. split; [exact Hqf|].
      split; [exact Hfit|].
      unfold gfits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
      destruct (Hbs _ K2 Hff E2) as [f Ef']. cbn [static_upper_bound] in Hst2. rewrite Hst2 in Ef'. exists f. exact Ef'. }
    (* the object, as c: below the receiver as c, instantiated *)
    set (D := RootResolved mr c (map (instantiate env sigma) ys')).
    assert (HgD: ground env D = true).
    { unfold ground, D. apply andb_true_iff. split.
      - apply make_root_gfrag; [rewrite length_map; exact Hly|]. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        destruct (Hys a Ha) as [_ [_ [_ [Hw Hb']]]].
        destruct (wide_argument env wf sigma KR Hsf a Hw Hb') as [v [o [n' [_ [_ [_ [_ [_ [Hg _]]]]]]]]]. exact Hg.
      - change (forallb no_refs (map (instantiate env sigma) ys') = true). apply forallb_forall.
        intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. destruct (Hys a Ha) as [_ [_ [_ [Hw Hb']]]].
        destruct (wide_argument env wf sigma KR Hsf a Hw Hb') as [v [o [n' [_ [_ [_ [_ [_ [_ [Hn _]]]]]]]]]]. exact Hn. }
    assert (HRD: exists f, unify env f D (instantiate env sigma (RootResolved ma ca ys)) (Ongoing []) = Some (Ongoing [])).
    { destruct (below_refl env wf declared declared_wf terminates finite not_expansive D (ground_of_fragment env declared D HgD)) as [[|f] Ef];
          [discriminate Ef|].
      exists (S f). rewrite instantiate_class. unfold D in Ef |- *. rewrite unify_classes in Ef |- *.
      replace (base_type_is_subtype_of env c c) with true in Ef by (unfold base_type_is_subtype_of; rewrite class_eqb_refl; reflexivity).
      rewrite mutability_is_subtype_of_refl, (class_eqb_false c nothing Hc), class_eqb_refl in Ef.
      rewrite Hbca, (assignment_mutability_of_class env ma ca (map (instantiate env sigma) ys) ys),
          (assignment_mutability_of_class env mr c (map (instantiate env sigma) ys') (map receiver_leaf cvars)), Hmr, (class_eqb_false ca nothing Hca).
      unfold unify_arguments in Ef |- *. rewrite Hcomm. exact Ef. }
    pose proof (in_fragment_ground env _ Hfo) as Hgo.
    assert (Hobj': exists f, unify env f (instantiate env sigma (RootResolved ma ca ys)) (RootResolved mo e xs) (Ongoing []) = Some (Ongoing [])).
    { exists n0. unfold is_assignable_to, empty_unification in Hobj.
      destruct (unify env n0 (instantiate env sigma (RootResolved ma ca ys)) (RootResolved mo e xs) (Ongoing [])) as [[w|]|] eqn:E;
          try discriminate Hobj.
      rewrite <- E. rewrite (ground_keeps env wf n0 _ _ [] w HgR Hgo E) in E. exact E. }
    destruct (rtrans _ _ _ Hgo HgR HgD Hobj' HRD) as [[|f1] E1]; [discriminate E1|].
    unfold D in E1. rewrite unify_classes in E1.
    destruct (base_type_is_subtype_of env e c) eqn:Hbe; [|discriminate E1].
    match type of E1 with context [if Model.is_subtype_of ?x ?y then _ else _] =>
        destruct (Model.is_subtype_of x y); [|discriminate E1] end.
    rewrite (class_eqb_false e nothing He), <- Hzs in E1.
    pose proof (object_arguments_exact env wf c mo e xs zs He Hbe Hfo Hxx Hzs) as Hzx.
    assert (Hfz: forall z, In z zs -> argument_gfrag env z = true).
    { intros z Hz. pose proof (Hzx z Hz) as Ez. destruct z as [| | | |[] o x| |]; try discriminate Ez.
      apply andb_true_iff in Ez. exact (in_fragment_is_gfrag env x (proj2 Ez)). }
    assert (Hlz: length (map (instantiate env sigma) ys') = length zs).
    { rewrite length_map, Hly. subst zs. destruct (Class_eq_dec e c) as [<-|Hne].
      - rewrite class_eqb_refl. exact (eq_sym (proj1 (root_in_fragment env mo e xs Hfo))).
      - rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
        exact (eq_sym (proj1 (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs))). }
    pose proof (pairwise_of_arguments env f1 (map (instantiate env sigma) ys') zs [] Hlz
        (fun t a w Ht Ha E => gkeeps_arguments env wf f1 t a [] w
            ltac:(apply in_map_iff in Ht; destruct Ht as [y [<- Hy]]; destruct (Hys y Hy) as [_ [_ [_ [Hw Hb']]]];
                  destruct (wide_argument env wf sigma KR Hsf y Hw Hb') as [v [o [n' [_ [_ [_ [_ [_ [Hg _]]]]]]]]]; exact Hg)
            (Hfz a Ha) E) E1) as Hpw.
    (* the bindings at run time *)
    assert (Hlookup: forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ ground env x = true
        /\ exists f, unify env f bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. rewrite Hbdef, lookup_app. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(rewrite length_map in Hlz; lia) Hi) as [z Hz].
        rewrite (lookup_parameter env wf c zs i p z Hpi Hz).
        destruct (Hzb i p bound z Hi Hz) as [o [x [f [-> Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        exists o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact (in_fragment_ground env x Hx)|]. exists f. exact Ef.
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
        assert (Hndo: NoDup (map fst ovars)).
        { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
          inversion H. apply IH. assumption. }
        rewrite (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U (fst v))))
            p bound Hndo Hin).
        cbn [fst]. exists ref, (instantiate env sigma (final_value_of env U p)). split; [reflexivity|]. split; [reflexivity|].
        destruct (Hfin p bound Hin) as [st [_ [_ [_ [Hff [Hqf [_ [f Ef]]]]]]]].
        destruct (instance_ground _ Hqf) as [Kf [_ Hgf]]. split; [exact Hgf|].
        destruct (HQbounds p bound Hin) as [Hcb Hclb].
        pose proof (Hbounds p bound (in_or_app _ _ _ (or_intror Hin))) as Hfb.
        destruct (subst_below _ bound Hqf Hcb (ex_intro _ f Ef))
            as [f' Ef'].
        rewrite (instantiate_class_types (depth bound) bound (le_n _) Hfb Hclb) in Ef'. exists f'. exact Ef'. }
    destruct (uniform_fuel_list vars (fun f v => forall o x, lookup_binding b (fst v) = Some (TypeArgument Model.invariant o x) ->
        unify env f (snd v) x (Ongoing []) = Some (Ongoing []))) as [K HK].
    { intros f f' v Hle E o x Hx. exact (unify_fuel_monotone env f f' _ _ _ _ Hle (E o x Hx)). }
    { intros [p bound] Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [_ [_ [f Ef]]]]]].
      exists f. intros o' x' Hx'. cbn [fst snd] in Hx' |- *. rewrite Hl' in Hx'. injection Hx' as <- <-. exact Ef. }
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (to_generic P) = true).
    { intros P' HP'. apply (bound_in_from_refs env wf vars _ _ P' (or_introl (proj1 (HPs P' HP'))) (proj2 (HPs P' HP'))).
      - intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [Ho [Hx _]]]]].
        unfold binds_exactly. rewrite Hl', Ho, (ground_gfrag env x Hx). unfold respects. pose proof (HK (p, bound) Hin o x Hl') as E1'.
        cbn [snd] in E1'. rewrite E1'. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    assert (Hbv: forall p o z, lookup_binding b p = Some (TypeArgument Model.invariant o z) -> is_exact_ownership o = true /\ ground env z = true).
    { intros p o z Hpb. assert (Hin: exists bound, In (p, bound) vars).
      { rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
        - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
          rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
          simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
        - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U q))) p _ Hpb)
              as [_ Hin]. apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
          exists bound. apply in_or_app. right. exact Hin. }
      destruct Hin as [bound Hin]. destruct (Hlookup p bound Hin) as [o' [x [Hl' [Ho [Hx _]]]]]. rewrite Hl' in Hpb.
      injection Hpb as <- <-. split; [exact Ho|exact Hx]. }
    assert (Hbnone: forall q, ~ In q (map fst vars) -> lookup_binding b q = None).
    { intros q Hq. rewrite Hbdef, lookup_app.
      assert (Hnc: ~ In q (parameter_ids env c)).
      { rewrite <- Hids. intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. left. exact Hin. }
      rewrite (lookup_combine_none _ zs q Hnc: lookup_binding (bindings_of env c zs) q = None).
      apply (lookup_map_none ovars (fun v => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U (fst v)))) q).
      intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. right. exact Hin. }
    (* what the type variables stand for at run time *)
    assert (Hdom: dom b u).
    { intros p o z Hpb. destruct (Hbv p o z Hpb) as [_ _].
      rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Ev) as [y Hy].
        eexists. exact (Hcap i p bound y Ev Hy).
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U q))) p _ Hpb)
            as [_ Hin]. apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        eexists. exact (Hownu p bound Hin). }
    assert (Hrsat: rsat b U).
    { intros p o z Hpb. pose proof Hpb as Hpb0. rewrite Hbdef, lookup_app in Hpb.
      destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - (* a type parameter of c: the type argument of the object, within that of the receiver, instantiated *)
        injection Hpb as ->. destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi Hz]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Ev) as [y Hy].
        exists (mkVariableState bound y y true true). split; [exact (Hkeep p _ (Hcap i p bound y Ev Hy) eq_refl)|].
        destruct (Hys y (nth_error_In _ _ Hy)) as [Hgy [Hry [[HcX Hmy] _]]].
        destruct y as [| | | |vb ob X| |]; try discriminate Hgy.
        unfold rfits. cbn [is_exact upper_bound lower_bound].
        pose proof (Forall2_nth_error _ zs (map (instantiate env sigma) ys') i _ _ Hpw Hz (map_nth_error _ i _ Hy)) as Ezy.
        destruct f1 as [|K1]; [discriminate Ezy|].
        exists vb, ob, X, K1. split; [reflexivity|]. split; [reflexivity|]. split; [split; [exact Hgy|exact Hry]|].
        split; [exact HcX|]. split; [exact (proj1 Hmy)|exact Ezy].
      - (* a type parameter of the function: its final value, instantiated *)
        destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U q))) p _ Hpb)
            as [Ea Hin]. injection Ea as Eo Ez. subst o z.
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (Hfin p bound Hin) as [st [HlU [He2 [_ [Hff [Hqf [Hfit _]]]]]]].
        exists st. split; [exact HlU|]. unfold rfits. rewrite He2. exists (final_value_of env U p).
        split; [exact Hff|]. split; [exact Hqf|]. split; [exact Hfit|reflexivity]. }
    (* each argument, in turn *)
    destruct (rfold b (fun x inner => let '(P', A') := x in unify env nf P' A' inner)
        (fun x => let '(P', A') := x in exists f, unify env f (inst env b P') (instantiate env sigma A') (Ongoing []) = Some (Ongoing []))
        (combine Ps As) u U) as [_ [_ [_ [_ Hall]]]].
    - intros [P' A']. apply unify_keeps_failure.
    - intros [P' A'] Hin s1 s1' Hs1 Hd1 E. apply in_combine_l in Hin as HP'. apply in_combine_r in Hin as HA'.
      pose proof (HAs' b Hbnone A' HA') as HyA.
      destruct (proj1 (generic_arguments env wf declared declared_wf terminates finite not_expansive intersect_in_fragment supertype_in_fragment
          intersect_below supertype_above caller (caller_argument env declared ps) (caller_argument_nested env declared ps)
          (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom' (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b K nf)
          P' A' s1 s1' (proj1 (HPs P' HP')) HyA (Hb P' HP') Hs1 E) as [Hs1' [Hm1 _]].
      split; [exact Hs1'|]. split; [exact Hm1|]. split; [exact (unify_keeps_exact env nf P' A' s1 s1' E)|].
      intros Hr. exact (proj1 (runtime_arguments b K Hbv nf) P' A' s1 s1' (proj1 (HPs P' HP')) HyA (Hb P' HP') Hs1 Hd1 E Hr).
    - exact Hwfu.
    - exact Hdom.
    - exact Hfold.
    - destruct (Hall Hrsat (P, A) HPA) as [f Ef]. exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.

End Receivers.

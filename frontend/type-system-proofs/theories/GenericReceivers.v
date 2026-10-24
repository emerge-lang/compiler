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
From EmergeTypeSystem Require Import FreeInstances.
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
(* The bounds of the type parameters of the function are class types without type parameters;     *)
(* generic_receiver_with_bounded_variables_sound, below, takes static upper bounds with type      *)
(* variables, as GenericArguments.v has them.                                                     *)
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
    intros b s s' Hs [Hk1 [Hk2 _]] Hd p o z Hp. destruct (Hd p o z Hp) as [st Hl]. destruct (is_exact st) eqn:Ee.
    - exists st. exact (Hk1 p st Hl Ee).
    - destruct (proj1 Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' _]]. exists st'. exact Hl'.
Qed.

(* What the variables stand for after a unification, they stand for before *)
Lemma rsat_back: forall b s s', gwf s -> keeps_exact s s' ->
    (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s) -> dom b s -> rsat b s' -> rsat b s.
Proof.
    intros b s s' Hs [Hk1 [Hk2 _]] Hmono Hdom H p o z Hp. destruct (Hdom p o z Hp) as [st Hl].
    destruct (H p o z Hp) as [st' [Hl' Hf']]. exists st. split; [exact Hl|].
    destruct (is_exact st) eqn:Ee.
    - rewrite (Hk1 p st Hl Ee) in Hl'. injection Hl' as <-. exact Hf'.
    - destruct (proj1 Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
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
      destruct (unify_keeps_exact env (S n) _ A s s' H) as [_ [Hk2 _]].
      destruct (proj1 Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
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
    - destruct (unify_keeps_exact env (S n) A _ s s' H) as [_ [Hk2 _]].
      destruct (proj1 Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
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

Lemma caller_nullable_assignee: forall A, gfrag env A = true -> caller A -> caller (nullable_assignee env A).
Proof.
    intros A HA HcA. destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        cbn [nullable_assignee]; [exact HcA|exact (caller_nullable env declared ps an HcA)|exact (caller_narrowed env wf declared ps _ HcA)|exact HcA].
Qed.

(* Without null, a type of the fragment is what a nullable type unifies its nested type with *)
Lemma without_null_nullable_assignee: forall x, gfrag env x = true -> without_null env x = nullable_assignee env x.
Proof.
    intros x Hx. destruct (gfrag_cases env x Hx) as [[m [c [args ->]]]|[[an [-> [Hn _]]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        try reflexivity.
    change (without_null env an = an). exact (without_null_unchanged env an (non_null_not_nullable env an Hn)).
Qed.

Lemma rewrap_sigma: forall Y, instantiate env sigma (rewrap_nullable Y) = rewrap_nullable (instantiate env sigma Y).
Proof.
    intros [m c args|n|g|me msg|v o n|g|cs]; try reflexivity.
    change (rewrap_nullable (instantiate env sigma n) = rewrap_nullable (rewrap_nullable (instantiate env sigma n))).
    destruct (instantiate env sigma n); reflexivity.
Qed.

(* At run time, a type variable made nullable: the type it stands for, Z or z without null, made
   nullable, takes what z takes without null *)
Lemma runtime_nullable_variable: forall A z Z f, gfrag env A = true -> caller A -> ground env z = true -> ground env Z = true ->
    without_null env Z = without_null env z ->
    unify env f z (instantiate env sigma (nullable_assignee env A)) (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' (rewrap_nullable Z) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros A z Z f HA HcA Hz HZ EZ H.
    destruct (instance_ground A HcA) as [_ [_ HgA]].
    destruct (instance_ground _ (caller_nullable_assignee A HA HcA)) as [_ [_ HgA0]].
    exists (S f). rewrite (ground_rewrap env Z HZ), (ground_nullable_target env f _ _ [] HgA), EZ.
    rewrite <- (instance_nullable_assignee A HA HcA).
    exact (ground_unify_without_null env f z _ [] [] Hz HgA0 H).
Qed.

(* At run time, a narrowed type variable: the type it stands for, Z or z without null, takes what z takes,
   where that is non-null *)
Lemma runtime_without_null: forall A z Z f, caller A -> ground env z = true -> ground env Z = true -> is_nullable env Z = false ->
    without_null env Z = without_null env z -> is_nullable env A = false ->
    unify env f z (instantiate env sigma A) (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' Z (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros A z Z f HcA Hz HZ HnZ EZ HnA H. destruct (instance_ground A HcA) as [K [HbA HgA]].
    destruct (inst_facts env wf sigma K Hsf A (proj1 HcA) HbA) as [_ [Hn _]].
    rewrite <- (ground_non_null_without_null env Z HZ HnZ), EZ, <- (ground_non_null_without_null env _ HgA (Hn HnA)).
    exists f. exact (ground_unify_without_null env f z _ [] [] Hz HgA H).
Qed.

Lemma shape_of_fragment: forall A, gfrag env A = true -> match A with Error _ _ | TypeVariable _ => False | _ => True end.
Proof.
    intros A HA. destruct (gfrag_cases env A HA) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I.
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
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)).
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
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hg.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
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
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)), instantiate_class.
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
        pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps)
            (caller_narrowed env wf declared ps) b A HA) as HyN.
        destruct (IHt _ _ s s' HP' HyN Hb' Hs Hd H Hr) as [f1 E1].
        pose proof (instance_ground_b _ HP' Hb') as HgP.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in E1, HgP.
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
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
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)), instantiate_class.
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
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in E1, HgP |- *.
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
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in E1, HgPn.
          rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)), unify_nullable_nullable.
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

(* A parameter, also of a type variable made nullable, at run time *)
Lemma runtime_parameter: forall n P A s s', pfrag env P = true -> no_given P = true -> yf A ->
    bound_in env b K [] (pgeneric P) = true -> gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
    exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n P A s s' HP Hg HA Hbp Hs Hd H Hr.
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsr _]]]]]|[gm [nn [p [-> [Hsr _]]]]]]].
    { rewrite (pgeneric_ifrag env wf P HP') in Hbp. exact (proj1 (runtime_arguments n) P A s s' HP' HA Hbp Hs Hd H Hr). }
    all: destruct gm; [discriminate Hg|].
    all: destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hbp) as [o [z [Ez _]]]; cbn [param_of] in Ez.
    all: destruct (Hb p o z Ez) as [_ Hz].
    all: destruct (Hr p o z Ez) as [st' [Hl' Hfit]].
    all: assert (Hfits: forall st'', lookup_state s' p = Some st'' -> rfits st'' o z)
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    all: assert (HZ: ground env (if nn then without_null env z else z) = true /\
        without_null env (if nn then without_null env z else z) = without_null env z)
        by (destruct nn; [exact (conj (ground_without_null env z Hz) (ground_without_null_idempotent env z Hz))|exact (conj Hz eq_refl)]).
    - (* the variable itself, narrowed or not *)
      destruct n as [|n]; [discriminate H|].
      destruct (unify_variable_given env wf n None nn p A s s' (shape_of_fragment A (proj1 (proj1 HA))) H) as [H1 [_ Hnul]].
      destruct (rtarget_leaf n p [] _ s s' Hs (proj1 HA) (proj1 (proj2 HA)) (proj2 (proj2 (proj2 HA))) H1 o z Hz Hfits) as [f Hf].
      rewrite (proj1 (inst_reference env b None nn p [] _ _ _ Ez)). unfold ref_apply. cbn zeta.
      destruct nn; [|exists f; exact Hf].
      apply (runtime_without_null A z _ f (proj2 (proj2 (proj2 HA))) Hz (proj1 HZ)
          (without_null_not_nullable env wf declared declared_wf z (ground_gfrag env z Hz)) (proj2 HZ)); [|exact Hf].
      destruct (is_nullable env A) eqn:EA; [|reflexivity].
      rewrite (narrowed_not_nullable env wf None p Hsr) in Hnul. discriminate (Hnul eq_refl).
    - (* made nullable: the variable takes the argument without null *)
      destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 (proj1 HA))) as [HgA0 _].
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_variable_given env wf n None nn p _ s s' (shape_of_fragment _ HgA0) H) as [H1 _].
      pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps) b A HA)
          as HA0.
      destruct (rtarget_leaf n p [] _ s s' Hs (proj1 HA0) (proj1 (proj2 HA0)) (proj2 (proj2 (proj2 HA0))) H1 o z Hz Hfits) as [f Hf].
      rewrite (proj2 (inst_reference env b None nn p [] _ _ _ Ez)). unfold ref_apply. cbn zeta.
      exact (runtime_nullable_variable A z _ f (proj1 (proj1 HA)) (proj2 (proj2 (proj2 HA))) Hz (proj1 HZ) (proj2 HZ) Hf).
Qed.

End Main.

(* ---------------------------------------------------------------------------------------------- *)
(* Capturing the type arguments of a receiver of generic code                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gcapture_step: forall n p bound s y u,
    lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true) -> no_vars bound = true ->
    argument_gfrag env y = true ->
    unify env n (receiver_leaf (p, bound)) y (Ongoing s) = Some (Ongoing u) ->
    u = set_state s p (mkVariableState bound y y true true).
Proof.
    intros n p bound s [| | | |vy oy Y| |] u Hl Hnv Hy H; simpl in Hy; try discriminate Hy.
    destruct n as [|n]; [discriminate H|].
    rewrite unify_step_once in H. unfold unify_step, unify_type_argument, receiver_leaf in H. cbn beta iota zeta in H.
    replace (ownership_is_assignable_to oy any_ownership) with true in H by (destruct oy; reflexivity).
    cbn [negb fst snd] in H. unfold capturable in H. cbn beta iota in H. rewrite Hl in H. cbn [is_capturable is_exact negb andb] in H.
    unfold plus_exact_binding in H. rewrite Hl in H. cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    rewrite (initial_closed bound Hnv) in H. unfold plus_binding_check, plus_static_check in H. cbn [static_upper_bound] in H.
    rewrite Hnv in H.
    destruct (unify env n bound Y (Ongoing s)) as [[w|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument vy oy Y) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    assert (H': Some (Ongoing (set_state w' p (mkVariableState bound (TypeArgument vy oy Y) (TypeArgument vy oy Y) true true)))
        = Some (Ongoing u)) by (destruct vy; exact H).
    injection H' as <-. f_equal.
    destruct n as [|n]; [discriminate E2|].
    destruct vy; rewrite unify_step_once in E2; unfold unify_step, unify_type_argument in E2; cbn beta iota zeta in E2;
        try (injection E2 as <-; reflexivity).
    - exact (gkeeps env wf n Y bottom_type s w' Hy (bottom_gfrag env wf) E2).
    - exact (gkeeps env wf n Y bottom_type s w' Hy (bottom_gfrag env wf) E2).
Qed.

Lemma gcapture_arguments: forall n vars ys s u,
    NoDup (map fst vars) -> length ys = length vars ->
    (forall y, In y ys -> argument_gfrag env y = true) ->
    (forall p bound, In (p, bound) vars -> no_vars bound = true) ->
    (forall p bound, In (p, bound) vars -> lookup_state s p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)) ->
    fold_unify (fun inner '(t, a) => unify env n t a inner) (combine (map receiver_leaf vars) ys) (Ongoing s) = Some (Ongoing u) ->
    (forall i p bound y, nth_error vars i = Some (p, bound) -> nth_error ys i = Some y ->
        lookup_state u p = Some (mkVariableState bound y y true true))
    /\ (forall q, ~ In q (map fst vars) -> lookup_state u q = lookup_state s q).
Proof.
    intros n vars. induction vars as [|[p bound] rest IH]; intros [|y ys] s u Hnd Hl Hys Hnv Hvars H; simpl in Hl; try discriminate Hl.
    - simpl in H. injection H as <-. split; [intros [|i]; discriminate|reflexivity].
    - inversion Hnd as [|? ? Hnotin Hnd']. subst.
      simpl in H. destruct (unify env n (receiver_leaf (p, bound)) y (Ongoing s)) as [[s1|]|] eqn:E;
          [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      pose proof (gcapture_step n p bound s y s1 (Hvars p bound (or_introl eq_refl)) (Hnv p bound (or_introl eq_refl)) (Hys y (or_introl eq_refl)) E) as ->.
      destruct (IH ys (set_state s p (mkVariableState bound y y true true)) u Hnd' ltac:(lia) (fun y' Hy' => Hys y' (or_intror Hy')) (fun q bq Hin => Hnv q bq (or_intror Hin)))
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
    (forall P, In P Ps -> pfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (forall P, In P Ps -> no_given P = true) ->
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ owners_outside env (map fst (cvars ++ ovars)) A
        /\ caller A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs
        ++ map (fun v => (fst v, TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U (fst v))))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f (instantiate env sigma A) (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds HQbounds HfR HcR Hrec
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HPg HAs Hfold b Hbdef P A HPA.
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) (map fst cvars)))) vars).
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
    assert (Hfresh: forall p bound, In (p, bound) cvars -> lookup_state s0 p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)).
    { intros p bound Hin. unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin).
      reflexivity. }
    destruct (gcapture_arguments n cvars ys' s0 u Hndc Hl (fun y Hy => proj1 (Hys y Hy))
        (fun p bound Hin => in_fragment_no_vars env bound (Hbounds p bound (in_or_app _ _ _ (or_introl Hin)))) Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variable states unify works with *)
    assert (Hu: forall p st, lookup_state u p = Some st ->
        (exists i bound y, nth_error cvars i = Some (p, bound) /\ nth_error ys' i = Some y /\ st = mkVariableState bound y y true true)
        \/ (exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
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
          cbn [static_upper_bound]. split; [exact Hny|]. split; [exact Hny|]. split; [intros E; discriminate E|].
          exact (no_vars_in _ _ (in_fragment_no_vars env bound (Hbounds p bound (in_or_app _ _ _ (or_introl (nth_error_In _ _ Hi)))))).
        + pose proof (Hbounds p bound (in_or_app _ _ _ (or_intror Hin))) as Hfb.
          cbn [static_upper_bound]. rewrite (initial_in_fragment env bound Hfb).
          split; [exact (of_fragment_no_vars env declared bound (of_fragment_of_class env declared bound Hfb))|]. split; [reflexivity|]. split.
          * intros _. split; [reflexivity|]. split; [exists 2; apply (below_all env wf [] bound 2 Hfb); lia|].
            split; [exact (of_fragment_of_class env declared bound Hfb)|]. split; [exact (bottom_of_fragment env wf declared)|].
            unfold static_ok. cbn [static_upper_bound]. rewrite (in_fragment_no_vars env bound Hfb). intros x f _ Ex; exists f; exact Ex.
          * exact (no_vars_in _ _ (in_fragment_no_vars env bound Hfb)).
      - intros p st Hp He'. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]]; [discriminate He'|].
        cbn [upper_bound lower_bound static_upper_bound]. rewrite (initial_in_fragment env bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin)))).
        split; [exact (proj1 (HQbounds p bound Hin))|]. split; [exact caller_bottom'|].
        exact (in_fragment_no_vars env bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin)))). }
    (* the generic inference: its variable states, and the final values *)
    assert (HAs': forall b', (forall q, ~ In q (map fst vars) -> lookup_binding b' q = None) -> forall A, In A As -> yfrag env declared caller b' A).
    { intros b' Hb' A' HA'. destruct (HAs A' HA') as [Hf [Hbo [Ho Hq]]]. split; [exact Hf|]. split; [exact Hbo|].
      split; [exact (owners_outside_free env wf _ b' Hb' A' Ho)|exact Hq]. }
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (uniform_fuel_list vars (fun f v => unify env f (snd v) (snd v) (Ongoing []) = Some (Ongoing []))) as [K0 HK0].
    { intros f f' v Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { intros [p bound] Hin. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (pgeneric P) = true).
    { intros P' HP'. apply (pbound_in_from_refs env wf vars _ _ P' (proj1 (HPs P' HP')) (proj2 (HPs P' HP'))).
      - intros p bound Hin. unfold binds_exactly, b0. rewrite (lookup_map_vars vars _ p bound Hnd' Hin). cbn [snd].
        rewrite (in_fragment_is_gfrag env _ (Hbounds p bound Hin)). unfold respects. pose proof (HK0 (p, bound) Hin) as E0.
        cbn [snd] in E0. rewrite E0. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (ginv nf Ps As u U b0 K0 Hwfu (fun P' HP' => conj (proj1 (HPs P' HP')) (Hb0 P' HP'))
        (HAs' b0 (fun q Hq => lookup_map_none vars _ q Hq)) Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep [Hkeep2 _]].
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ final_value_of env U p = Constraints.final_value env st /\ of_fragment env declared (final_value_of env U p)
        /\ caller (final_value_of env U p) /\ gfits env declared st ref (final_value_of env U p)
        /\ exists f, unify env f bound (final_value_of env U p) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      destruct (proj1 HwfU p st2 HlU) as [_ [_ [Hw _]]]. destruct (Hw He2) as [_ [_ [Hbu [Hbl Hbs]]]].
      destruct (proj2 HwfU p st2 HlU He2) as [Hqu [Hql Hsc]]. unfold static_ok in Hbs. rewrite Hsc in Hbs.
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
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true).
    { intros P' HP'. apply (pbound_in_from_refs env wf vars _ _ P' (proj1 (HPs P' HP')) (proj2 (HPs P' HP'))).
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
      destruct (generic_parameter env wf declared declared_wf terminates finite not_expansive intersect_in_fragment supertype_in_fragment
          intersect_below supertype_above caller (caller_argument env declared ps) (caller_argument_nested env declared ps)
          (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom' (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b K nf
          P' A' s1 s1' (proj1 (HPs P' HP')) HyA (Hb P' HP') Hs1 E) as [Hs1' [Hm1 _]].
      split; [exact Hs1'|]. split; [exact Hm1|]. split; [exact (unify_keeps_exact env nf P' A' s1 s1' E)|].
      intros Hr. exact (runtime_parameter b K Hbv nf P' A' s1 s1' (proj1 (HPs P' HP')) (HPg P' HP') HyA (Hb P' HP') Hs1 Hd1 E Hr).
    - exact Hwfu.
    - exact Hdom.
    - exact Hfold.
    - destruct (Hall Hrsat (P, A) HPA) as [f Ef]. exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Receivers of generic code, for functions whose bounds mention type variables                   *)
(*                                                                                                *)
(* As above, with the variable states of GenericArguments.v for static upper bounds with type     *)
(* variables (gwf2). The type parameters of the callee are bound in b to types of generic code:   *)
(* those of the class to the type arguments of the object, those of the function to their final   *)
(* values; at run time, a type of the parameters stands for that, instantiated by sigma (rinst).   *)
(* Checking a lower bound against a static upper bound with type variables unifies the bound with  *)
(* the candidate in it, a mixed type (mfrag), so inference is shown sound at run time for mixed    *)
(* types (runtime_mixed). Their references to Nothing are `exclusive Nothing` (nothing_is_bottom). *)
(* ---------------------------------------------------------------------------------------------- *)

Section Bounded.

Hypothesis supertype_bottom_only: closest_common_supertype_keeps_bottom_only env declared.

Let Qa := caller_argument env declared ps.
Let gw := gwf2 env declared caller.

Let gleaf (k: nat) (b: Bindings) := gleaf_all env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
    not_expansive intersect_in_fragment supertype_in_fragment intersect_below supertype_above caller Qa
    (caller_argument_nested env declared ps) (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom'
    (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
    (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_supertype_arguments env wf declared ps)
    supertype_bottom_only k b.

(* What the type variables stand for at run time: the types b binds them to, instantiated *)
Definition rsat2 (b: Bindings) (s: VariableStates): Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        exists st, lookup_state s p = Some st /\ rfits st o (instantiate env sigma x).

(* A type of the parameters at run time *)
Definition rinst (b: Bindings) (t: EType): EType := instantiate env sigma (instantiate_free env b t).

Lemma rinst_root: forall b m c args, rinst b (RootResolved m c args) = RootResolved m c (map (rinst b) args).
Proof. intros b m c args. unfold rinst. cbn [instantiate_free]. rewrite instantiate_class, map_map. reflexivity. Qed.

Lemma rinst_nullable: forall b m c args, rinst b (Nullable (RootResolved m c args)) = Nullable (rinst b (RootResolved m c args)).
Proof.
    intros b m c args. unfold rinst. cbn [instantiate_free rewrap_nullable].
    change (instantiate env sigma (Nullable (RootResolved m c (map (instantiate_free env b) args))))
        with (rewrap_nullable (instantiate env sigma (RootResolved m c (map (instantiate_free env b) args)))).
    rewrite instantiate_class. reflexivity.
Qed.

Lemma map_rinst: forall b l, map (rinst b) l = map (instantiate env sigma) (map (instantiate_free env b) l).
Proof. intros b l. rewrite map_map. reflexivity. Qed.

Lemma dom_forward2: forall b s s', gw s -> keeps_exact s s' -> dom b s -> dom b s'.
Proof.
    intros b s s' Hs [Hk1 [Hk2 _]] Hd p o z Hp. destruct (Hd p o z Hp) as [st Hl]. destruct (is_exact st) eqn:Ee.
    - exists st. exact (Hk1 p st Hl Ee).
    - destruct (Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' _]]. exists st'. exact Hl'.
Qed.

(* What the variables stand for after a unification, they stand for before *)
Lemma rsat_back2: forall b s s', gw s -> keeps_exact s s' ->
    (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s) -> dom b s -> rsat2 b s' -> rsat2 b s.
Proof.
    intros b s s' Hs [Hk1 [Hk2 _]] Hmono Hdom H p o x Hp. destruct (Hdom p o x Hp) as [st Hl].
    destruct (H p o x Hp) as [st' [Hl' Hf']]. exists st. split; [exact Hl|].
    destruct (is_exact st) eqn:Ee.
    - rewrite (Hk1 p st Hl Ee) in Hl'. injection Hl' as <-. exact Hf'.
    - destruct (Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st'' [Hl'' [He'' _]]]. rewrite Hl' in Hl''. injection Hl'' as <-.
      unfold rfits in Hf' |- *. rewrite He'' in Hf'. rewrite Ee. destruct Hf' as [x' [Hx [Hc [Hg Ez]]]].
      exists x'. split; [exact Hx|]. split; [exact Hc|]. split; [|exact Ez].
      assert (Hs1: gsatisfies env declared [(p, TypeArgument Model.invariant o x')] s').
      { intros q o' x'' Hq. simpl in Hq. destruct (param_eqb q p) eqn:Eq; [|discriminate Hq]. apply param_eqb_eq in Eq. subst q.
        injection Hq as <- <-. split; [exact Hx|]. exists st'. split; [exact Hl'|exact Hg]. }
      destruct (Hmono _ Hs1 p o x') as [_ [st0 [Hl0 Hg0]]]; [simpl; rewrite param_eqb_refl; reflexivity|].
      rewrite Hl in Hl0. injection Hl0 as <-. exact Hg0.
Qed.

(* A fold of steps that keep the variable states unify works with, at run time *)
Lemma rfold2: forall (b: Bindings) {X: Type} (h: X -> Unification -> option Unification) (Q: X -> Prop) l s s',
    (forall x, h x Failed = Some Failed) ->
    (forall x, In x l -> forall s0 s0', gw s0 -> dom b s0 -> h x (Ongoing s0) = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> Q x)) ->
    gw s -> dom b s -> fold_unify (fun inner x => h x inner) l (Ongoing s) = Some (Ongoing s') ->
    gw s' /\ dom b s' /\ (rsat2 b s' -> rsat2 b s) /\ keeps_exact s s' /\ (rsat2 b s' -> forall x, In x l -> Q x).
Proof.
    intros b X h Q l. induction l as [|x l IH]; intros s s' Hf Hstep Hs Hd H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [exact Hd|]. split; [auto|]. split; [apply keeps_exact_refl|]. intros _ x [].
    - destruct (h x (Ongoing s)) as [[s1|]|] eqn:E.
      + destruct (Hstep x (or_introl eq_refl) s s1 Hs Hd E) as [Hs1 [Hm1 [Hk1 HQ1]]].
        pose proof (dom_forward2 b s s1 Hs Hk1 Hd) as Hd1.
        destruct (IH s1 s' Hf (fun x' Hx' => Hstep x' (or_intror Hx')) Hs1 Hd1 H) as [Hs' [Hd' [Hback [Hk' Hall]]]].
        split; [exact Hs'|]. split; [exact Hd'|].
        split; [intros Hr; exact (rsat_back2 b s s1 Hs Hk1 Hm1 Hd (Hback Hr))|].
        split; [exact (keeps_exact_trans _ _ _ Hk1 Hk')|].
        intros Hr x' [<-|Hx']; [exact (HQ1 (Hback Hr))|exact (Hall Hr x' Hx')].
      + exfalso. clear -H Hf. induction l as [|y l IHl]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHl H).
      + discriminate H.
Qed.

(* What the variable takes, at run time *)
Lemma rtarget_leaf2: forall n b p bnd A s s', gw s -> yfrag env declared caller b A ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    forall o z, ground env z = true -> (forall st', lookup_state s' p = Some st' -> rfits st' o z) ->
    exists f, unify env f z (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n b p bnd A s s' Hs HA H o z Hz Hfit.
    destruct (proj1 (gleaf n b) p bnd A s s' Hs HA H) as [_ [_ Hsnd]].
    pose proof (proj2 (proj2 (proj2 HA))) as HcA.
    destruct (instance_ground A HcA) as [KA [_ HgA]].
    pose proof (variable_target_step env n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
    unfold plus_supertype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: by the type argument, instantiated *)
      destruct (keeps_free env wf n _ A s s' (proj1 (proj2 (Hs p st Hl))) (of_fragment_no_vars env declared A (proj1 HA)) H') as [-> _].
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
    - (* between bounds: a type of generic code between them, instantiated *)
      destruct (unify_keeps_exact env (S n) _ A s s' H) as [_ [Hk2 _]].
      destruct (Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' [He' _]]].
      pose proof (Hfit st' Hl') as Hf. unfold rfits in Hf. rewrite He' in Hf. destruct Hf as [x [Hx [Hcx [Hg ->]]]].
      apply (subst_below A x HcA Hcx). apply (Hsnd o x Hx). intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hg.
Qed.

(* What the variable is assigned to, at run time *)
Lemma rassignee_leaf2: forall n b p bnd A s s', gw s -> yfrag env declared caller b A ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
    forall o z, ground env z = true -> (forall st', lookup_state s' p = Some st' -> rfits st' o z) ->
    exists f, unify env f (instantiate env sigma A) z (Ongoing []) = Some (Ongoing []).
Proof.
    intros n b p bnd A s s' Hs HA H o z Hz Hfit.
    destruct (proj2 (gleaf n b) p bnd A s s' Hs HA H) as [_ [_ Hsnd]].
    pose proof (proj2 (proj2 (proj2 HA))) as HcA.
    destruct (instance_ground A HcA) as [KA [_ HgA]].
    pose proof (variable_assignee_step env n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
    unfold plus_subtype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (is_exact st) eqn:Ee.
    - destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars env declared A (proj1 HA)) (proj1 (Hs p st Hl)) H') as [-> _].
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
    - destruct (unify_keeps_exact env (S n) A _ s s' H) as [_ [Hk2 _]].
      destruct (Hs p st Hl) as [_ [_ [Hw _]]]. destruct (Hw Ee) as [Hcap _].
      destruct (Hk2 p st Hl Ee Hcap) as [st' [Hl' [He' _]]].
      pose proof (Hfit st' Hl') as Hf. unfold rfits in Hf. rewrite He' in Hf. destruct Hf as [x [Hx [Hcx [Hg ->]]]].
      apply (subst_below x A Hcx HcA). apply (Hsnd o x Hx). intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hg.
Qed.

(* Ownerships, instantiated *)
Lemma ownership_sigma: forall oa ot, ownership_is_assignable_to oa ot = true ->
    ownership_is_assignable_to (instantiate_ownership sigma oa) (instantiate_ownership sigma ot) = true.
Proof.
    intros oa ot H. destruct ot as [| | |p].
    - destruct oa; try discriminate H. reflexivity.
    - destruct oa; try discriminate H. reflexivity.
    - reflexivity.
    - destruct oa as [| | |q]; try discriminate H. simpl in H. apply param_eqb_eq in H. subst q. apply ownership_refl.
Qed.

Lemma ownership_concrete: forall oa ot, is_parameter_ownership ot = false -> ownership_is_assignable_to oa ot = true ->
    ownership_is_assignable_to (instantiate_ownership sigma oa) ot = true.
Proof.
    intros oa ot Hot H. destruct oa as [| | |q]; [exact H..|].
    destruct ot as [| | |p]; try discriminate Hot; try discriminate H. reflexivity.
Qed.

Lemma ownership_concrete_flipped: forall op oa, is_parameter_ownership op = false -> ownership_is_assignable_to op oa = true ->
    ownership_is_assignable_to op (instantiate_ownership sigma oa) = true.
Proof.
    intros op oa Hop H. destruct oa as [| | |q]; [exact H..|].
    destruct op; try discriminate Hop; discriminate H.
Qed.

(* Type arguments of generic code: what unify accepts of them, it does instantiated *)
Lemma subst_arguments: forall n t a, Qa t -> Qa a -> unify env n t a (Ongoing []) = Some (Ongoing []) ->
    exists f, unify env f (instantiate env sigma t) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n t a Ht Ha H.
    destruct t as [| | | |vt ot nt| |]; try (destruct Ht as [Ht _]; contradiction Ht).
    destruct a as [| | | |va oa na| |]; try (destruct Ha as [Ha _]; contradiction Ha).
    destruct Ht as [HcT [Hmt _]]. destruct Ha as [HcA [Hma _]].
    destruct (instance_of_argument vt ot nt HcT Hmt) as [ET HgT].
    destruct (instance_of_argument va oa na HcA Hma) as [EA HgA].
    assert (Hnt: is_type_variable nt = false) by (destruct nt; try reflexivity; destruct HcT as [Hw _]; discriminate Hw).
    destruct n as [|n]; [discriminate H|].
    rewrite (unify_type_arguments env n vt ot nt va oa na [] Hnt) in H.
    destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
    assert (Hgoal: forall f, compare_variances (unify env f) vt va (instantiate env sigma nt) (instantiate env sigma na) [] = Some (Ongoing []) ->
        unify env (S f) (instantiate env sigma (TypeArgument vt ot nt)) (instantiate env sigma (TypeArgument va oa na)) (Ongoing [])
            = Some (Ongoing [])).
    { intros f E. rewrite ET, EA.
      rewrite (unify_type_arguments env f vt _ (instantiate env sigma nt) va _ (instantiate env sigma na) [] (gfrag_not_variable env _ (ground_gfrag env _ HgT))).
      rewrite (ownership_sigma oa ot Ho). exact E. }
    pose proof (wide_no_vars env wf nt (proj1 HcT)) as Hnvt. pose proof (wide_no_vars env wf na (proj1 HcA)) as Hnva.
    destruct vt, va; unfold compare_variances in H; try discriminate H.
    1: { destruct (unify env n nt na (Ongoing [])) as [[w|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
         destruct (keeps_free env wf n nt na [] w Hnvt Hnva E1) as [-> _].
         destruct (subst_below na nt HcA HcT (ex_intro _ n E1)) as [f1 Hf1].
         destruct (subst_below nt na HcT HcA (ex_intro _ n H)) as [f2 Hf2].
         exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
         rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
         exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
    all: first
        [ destruct (subst_below na nt HcA HcT (ex_intro _ n H)) as [f Hf]
        | destruct (subst_below nt na HcT HcA (ex_intro _ n H)) as [f Hf]
        | destruct (subst_below top_type nt caller_top' HcT (ex_intro _ n H)) as [f Hf]
        | destruct (subst_below nt bottom_type HcT caller_bottom' (ex_intro _ n H)) as [f Hf] ];
        exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
Qed.

Section RuntimeMixed.

(* The bindings of the type parameters of the callee: to types of generic code *)
Variable b: Bindings.
Hypothesis Hpb: plain_values b.
Hypothesis Hbv: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x.

Let Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x :=
    fun q o x E => proj1 (Hbv q o x E).
Let yf := yfrag env declared caller b.
Let ayf := argument_yfrag env declared Qa b.

Let gm (n: nat) := mixed_arguments env wf declared declared_wf terminates finite not_expansive caller Qa
    (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_root env declared ps) (caller_nullable env declared ps)
    (caller_bound env wf declared ps) (caller_narrowed env wf declared ps) (caller_component env declared ps)
    (caller_supertype_arguments env wf declared ps) b Hpb Hbf gw (gwf2_capturable env declared caller) n (fun k _ => gleaf k b).

(* What unify does with a mixed type and a type of the arguments, at the fuel n, at run time *)
Definition rstep (n: nat): Prop :=
    (forall P A s s', mfrag env declared caller b P -> caller (instantiate_free env b P) -> mbinds b P -> nothing_is_bottom P = true ->
        yf A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
        exists f, unify env f (rinst b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', mfrag env declared caller b P -> caller (instantiate_free env b P) -> mbinds b P -> nothing_is_bottom P = true ->
        yf A -> gw s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
        exists f, unify env f (instantiate env sigma A) (rinst b P) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', margument env declared caller b P -> Qa (instantiate_free env b P) -> mbinds b P -> nothing_is_bottom P = true ->
        ayf A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
        exists f, unify env f (rinst b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', margument env declared caller b P -> Qa (instantiate_free env b P) -> mbinds b P -> nothing_is_bottom P = true ->
        ayf A -> gw s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
        exists f, unify env f (instantiate env sigma A) (rinst b P) (Ongoing []) = Some (Ongoing [])).

(* A type variable bound in b, at run time *)
Lemma rinst_variable: forall p bnd o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    rinst b (TypeVariable (mkGenericRef None false p bnd)) = instantiate env sigma x.
Proof. intros p bnd o x Ex. unfold rinst. rewrite (free_variable env b Hpb p bnd o x Ex). reflexivity. Qed.

(*
 * Inference is sound at run time for mixed types: what unify accepts of an argument of generic code
 * for a mixed type, the argument instantiated takes, with the type variables replaced by what they
 * stand for at run time (rsat2), and the types of generic code in the mixed type instantiated.
 *)
Lemma runtime_mixed: forall n, rstep n.
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    destruct (gm n) as [Gt [Ga [Gat Gaa]]].
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', gw s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat2 b s0' -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        gw s -> dom b s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        rsat2 b s' ->
        exists f, fold_unify (fun inner '(t, a) => unify env f t a inner) (combine (map inst_t targs) (map inst_a aargs)) (Ongoing [])
            = Some (Ongoing [])).
    { intros targs aargs s s' inst_t inst_a Hp Hs Hd H Hr.
      destruct (rfold2 b (fun x inner => let '(t, a) := x in unify env n t a inner)
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
    - (* a mixed type as the target *)
      intros P A s s' HP HcP HmP HnP HA Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      destruct (instance_ground _ HcP) as [KP [_ HgP]]. change (ground env (rinst b P) = true) in HgP.
      assert (Hroot: forall mt ct targs ma ca aargs, mfrag env declared caller b (RootResolved mt ct targs) ->
          caller (instantiate_free env b (RootResolved mt ct targs)) -> mbinds b (RootResolved mt ct targs) ->
          nothing_is_bottom (RootResolved mt ct targs) = true ->
          yf (RootResolved ma ca aargs) -> caller (RootResolved ma ca aargs) ->
          bound_in env sigma KA [] (RootResolved ma ca aargs) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (rinst b (RootResolved mt ct targs)) (instantiate env sigma (RootResolved ma ca aargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros mt ct targs ma ca aargs Hft HcT HmT HnT Hfa Hca Hba Hu.
        rewrite rinst_root, instantiate_class.
        destruct (mfrag_root env declared caller b mt ct targs Hft) as [_ Htargs].
        destruct (nothing_is_bottom_root mt ct targs HnT) as [_ Hntargs].
        destruct (yfrag_root env declared caller Qa (caller_root env declared ps) b ma ca aargs Hfa) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { exists 1. rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (rinst b) targs) targs),
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
            exact (proj2 (supertype_arguments_yfrag env wf declared Qa (caller_supertype_arguments env wf declared ps) b ca ct aargs
                Hne Hcn' Hbase Hla Haargs) a Ha). }
        destruct Hnorm as [Hnorm Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', gw s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat2 b s0' -> exists f, unify env f (rinst b t) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 Hd0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          pose proof (Hnorm a Ha) as Hya.
          destruct (Gat t a s0 s0' (Htargs t Ht) Hya Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. apply (IHat t a s0 s0' (Htargs t Ht)); try assumption.
          - exact (caller_root env declared ps mt ct (map (instantiate_free env b) targs) _ HcT (in_map _ _ _ Ht)).
          - exact (fold_and_in (mbinds b) targs HmT t Ht).
          - exact (Hntargs t Ht). }
        destruct (Hpairs targs norm s s' (rinst b) (instantiate env sigma) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (rinst b) targs) targs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (mfrag_cases env declared caller b P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm' [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HcP HmP HnP HA HcA HbA H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          pose proof (yfrag_generic env wf declared declared_wf caller (caller_bound env wf declared ps) b _ HA) as Hyb.
          destruct (IHt _ _ s s' HP HcP HmP HnP Hyb Hs Hd H Hr) as [f1 E1].
          set (g := mkGenericRef gm' nn q bq) in *.
          destruct (binds_ref_some env wf sigma KA [] g HbA) as [o [x [Ex [Ho [Hgx [Hresp Hbbq]]]]]].
          set (bd := effective_bound env g) in *.
          destruct (instance_ground bd (proj2 (proj2 (proj2 Hyb)))) as [Kb [_ Hgb]].
          destruct (instantiate_exact_generic env sigma g o x Ex Ho Hgx) as [EA _].
          rewrite (inst_nested_instantiate env wf sigma KA [] bd (proj1 (generic_of_wtfrag env wf _ (proj1 HcA))) Hbbq) in Hresp.
          rewrite EA in HgA |- *. unfold respects in Hresp.
          destruct (unify env KA (instantiate env sigma bd) (inst_ref env g x) (Ongoing [])) as [[w|]|] eqn:Ew;
              try discriminate Hresp.
          rewrite (ground_keeps env wf KA _ _ [] w Hgb HgA Ew) in Ew.
          exact (rtrans _ _ _ HgA Hgb HgP (ex_intro _ KA Ew) (ex_intro _ f1 E1)).
        * (* an intersection: through the component taken *)
          rewrite step_root_inter in H. destruct (flipped_some env n _ cs s s' H) as [c [Hc Ec]].
          destruct (yfrag_component env declared caller (caller_component env declared ps) b cs c HA Hc) as [Hyc _].
          destruct (IHt _ _ s s' HP HcP HmP HnP Hyc Hs Hd Ec Hr) as [f1 E1].
          pose proof (proj2 (proj2 (proj2 Hyc))) as Hcc. destruct (instance_ground c Hcc) as [Kc [_ Hgc]].
          destruct (subst_below _ c HcA Hcc (intersection_below_component env wf declared declared_wf terminates finite
              not_expansive cs c (proj1 HA) Hc)) as [f2 E2].
          exact (rtrans _ _ _ HgA Hgc HgP (ex_intro _ f2 E2) (ex_intro _ f1 E1)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
        pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps)
            (caller_narrowed env wf declared ps) b A HA) as HyN.
        assert (HcP': caller (instantiate_free env b (RootResolved mt ct targs))) by exact (caller_nullable env declared ps _ HcP).
        destruct (IHt _ _ s s' HP' HcP' HmP HnP HyN Hs Hd H Hr) as [f1 E1].
        destruct (instance_ground _ HcP') as [K' [_ HgPn]]. change (ground env (rinst b (RootResolved mt ct targs)) = true) in HgPn.
        rewrite rinst_root in E1, HgPn. rewrite rinst_nullable, rinst_root.
        destruct (instance_ground _ (proj2 (proj2 (proj2 HyN)))) as [KN [_ HgN]].
        pose proof (ground_non_null env f1 _ _ [] [] HgPn HgN eq_refl E1) as HnN.
        exists (S f1). rewrite (ground_nullable_target env f1 _ _ [] HgA).
        rewrite <- (instance_nullable_assignee A (proj1 (proj1 HA)) HcA), (ground_non_null_without_null env _ HgN HnN).
        exact E1.
      + (* a type variable *)
        destruct HmP as [a Ea]. destruct (Hpb p a Ea) as [_ [o [x [-> _]]]].
        rewrite (rinst_variable p bnd o x Ea). destruct (Hr p o x Ea) as [st' [Hl' Hf']].
        destruct (instance_ground x (proj2 (Hbv p o x Ea))) as [Kx [_ Hgx]].
        apply (rtarget_leaf2 n b p bnd A s s' Hs HA H o _ Hgx).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
    - (* a mixed type as the assignee *)
      intros P A s s' HP HcP HmP HnP HA Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      destruct (instance_ground _ HcP) as [KP [HbP HgP]]. change (ground env (rinst b P) = true) in HgP.
      assert (Hroot: forall ma ca aargs mp cp pargs, mfrag env declared caller b (RootResolved mp cp pargs) ->
          caller (instantiate_free env b (RootResolved mp cp pargs)) ->
          bound_in env sigma KP [] (instantiate_free env b (RootResolved mp cp pargs)) = true ->
          mbinds b (RootResolved mp cp pargs) -> nothing_is_bottom (RootResolved mp cp pargs) = true ->
          yf (RootResolved ma ca aargs) ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (instantiate env sigma (RootResolved ma ca aargs)) (rinst b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros ma ca aargs mp cp pargs Hfp Hcp Hbp Hmp Hnp Hfa Hu.
        rewrite rinst_root, instantiate_class.
        destruct (mfrag_root env declared caller b mp cp pargs Hfp) as [Hlp Hpargs].
        destruct (yfrag_root env declared caller Qa (caller_root env declared ps) b ma ca aargs Hfa) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { exists 1. rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (rinst b) pargs) pargs),
              (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        set (fp := map (instantiate_free env b) pargs).
        assert (Hfpc: forall y, In y fp -> Qa y) by (intros y Hy; exact (caller_root env declared ps mp cp fp y Hcp Hy)).
        assert (Hfpw: forall y, In y fp -> argument_wfrag env y = true /\ bound_in env sigma KP [] y = true).
        { intros y Hy. split; [exact (wtfrag_root_arguments env mp cp fp y (proj1 Hcp) Hy)|exact (bound_in_root env sigma KP [] mp cp fp Hbp y Hy)]. }
        pose proof (nothing_is_bottom_root mp cp pargs Hnp) as [_ Hnpargs].
        assert (Hnorm: (forall a, In a norm -> margument env declared caller b a /\ Qa (instantiate_free env b a) /\ mbinds b a
                /\ nothing_is_bottom a = true)
            /\ (if class_eqb cp ca then map (rinst b) pargs
                else parameterized_supertype_arguments env cp (map (rinst b) pargs) ca) = map (rinst b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne].
          - rewrite class_eqb_refl. split; [|reflexivity]. intros a Ha. split; [exact (Hpargs a Ha)|].
            split; [exact (Hfpc _ (in_map _ _ _ Ha))|]. split; [exact (fold_and_in (mbinds b) pargs Hmp a Ha)|exact (Hnpargs a Ha)].
          - rewrite (class_eqb_false _ _ Hne). pose proof (class_eqb_false_neq _ _ Hcn) as Hcn'.
            destruct (mixed_supertype_arguments env wf declared caller caller_bottom' b Hpb cp ca pargs Hne Hcn' Hbase Hlp Hpargs)
                as [Hcomm1 Hmn].
            assert (Hlfp: length fp = length (parameter_ids env cp)) by (unfold fp; rewrite length_map; exact Hlp).
            destruct (wide_supertype_arguments_commute env wf sigma KP Hsf cp ca fp Hne Hcn' Hbase Hlfp Hfpw) as [Hcomm2 _].
            assert (Hta: forall y, In y pargs -> is_type_argument y = true)
                by (intros y Hy; pose proof (Hpargs y Hy) as Hm'; destruct y; try contradiction; reflexivity).
            destruct (supertype_arguments_to_generic env wf cp ca pargs Hne Hcn' Hbase Hlp Hta) as [_ [_ [Hnb _]]].
            split.
            + intros a Ha. split; [exact (Hmn a Ha)|]. split.
              * apply (caller_supertype_arguments env wf declared ps cp ca fp Hne Hcn' Hbase Hlfp Hfpc).
                unfold fp. rewrite Hcomm1. exact (in_map _ _ _ Ha).
              * split; [exact (mixed_supertype_binds env wf declared caller b cp ca pargs Hne Hcn' Hbase Hlp Hpargs
                    (fold_and_in (mbinds b) pargs Hmp) a Ha)|].
                exact (Hnb Hnpargs a Ha).
            + rewrite !map_rinst. fold fp. rewrite Hcomm2. unfold fp. rewrite Hcomm1. reflexivity. }
        destruct Hnorm as [Hnormp Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', gw s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat2 b s0' -> exists f, unify env f (instantiate env sigma t) (rinst b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 Hd0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hma [Hca' [Hba' Hna']]]. pose proof (Haargs t Ht) as Hyt.
          destruct (Gaa a t s0 s0' Hma Hyt Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. exact (IHaa a t s0 s0' Hma Hca' Hba' Hna' Hyt Hs0 Hd0 E Hr0). }
        destruct (Hpairs aargs norm s s' (instantiate env sigma) (rinst b) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (rinst b) pargs) pargs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (mfrag_cases env declared caller b P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm' [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HcP HbP HmP HnP HA H).
        * rewrite unify_nullable_class in H.
          pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Hyn.
          destruct (IHa _ _ s s' HP HcP HmP HnP Hyn Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite rinst_root in E1, HgP |- *.
          rewrite unify_nullable_class. exact (ground_unify_without_null env f1 _ _ [] [] HgN HgP E1).
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          apply andb_true_iff in Ec. destruct Ec as [Ec _]. cbn [is_non_nullable_nothing] in Ec.
          destruct (nothing_is_bottom_root mp cp pargs HnP) as [Hb0 _]. specialize (Hb0 Ec).
          apply class_eqb_true in Ec. subst cp.
          destruct mp as [[]|], pargs; simpl in Hb0; try discriminate Hb0.
          exact (ground_takes_bottom _ HgA).
        * (* an intersection: each of its components takes it *)
          rewrite unify_step_once in H. unfold unify_step, unify_intersection in H.
          destruct (no_vars_filter cs (gfrag_components_no_vars env cs (proj1 (proj1 HA)))) as [Hvar Hnonvar].
          rewrite Hvar, Hnonvar in H. cbn zeta in H.
          set (Pc := RootResolved mp cp pargs) in *.
          destruct (fold_unify (fun inner component => unify env n component Pc inner) cs (Ongoing s)) as [[s2|]|] eqn:E1; try discriminate H.
          assert (Hstep: forall c, In c cs -> forall s0 s0', gw s0 -> dom b s0 -> unify env n c Pc (Ongoing s0) = Some (Ongoing s0') ->
              gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
              /\ (rsat2 b s0' -> exists f, unify env f (instantiate env sigma c) (rinst b Pc) (Ongoing []) = Some (Ongoing []))).
          { intros c Hc s0 s0' Hs0 Hd0 E. destruct (yfrag_component env declared caller (caller_component env declared ps) b cs c HA Hc) as [Hyc _].
            destruct (Ga Pc c s0 s0' HP Hyc Hs0 E) as [Hs0' [Hm0 _]].
            split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n c Pc s0 s0' E)|].
            intros Hr0. exact (IHa Pc c s0 s0' HP HcP HmP HnP Hyc Hs0 Hd0 E Hr0). }
          destruct (rfold2 b (fun c inner => unify env n c Pc inner)
              (fun c => exists f, unify env f (instantiate env sigma c) (rinst b Pc) (Ongoing []) = Some (Ongoing []))
              cs s s2 (fun c => unify_keeps_failure env n c Pc) Hstep Hs Hd E1) as [Hs2 [Hd2 [_ [_ Hall]]]].
          assert (Hr2: rsat2 b s2).
          { destruct (find_first (fun component => unify env n component Pc (Ongoing s2)) cs) as [[[cov s3]|]|] eqn:E2; try discriminate H.
            - cbn in H. injection H as <-. destruct (find_first_found _ _ _ _ E2) as [Hin E3].
              destruct (Hstep cov Hin s2 s3 Hs2 Hd2 E3) as [_ [Hm3 [Hk3 _]]].
              exact (rsat_back2 b s2 s3 Hs2 Hk3 Hm3 Hd2 Hr).
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
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm' [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * rewrite unify_class_nullable in H. discriminate H.
        * rewrite unify_nullable_nullable in H.
          pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Hyn.
          assert (HcP': caller (instantiate_free env b (RootResolved mp cp pargs))) by exact (caller_nullable env declared ps _ HcP).
          destruct (IHa _ _ s s' HP' HcP' HmP HnP Hyn Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          destruct (instance_ground _ HcP') as [K' [_ HgPn]]. change (ground env (rinst b (RootResolved mp cp pargs)) = true) in HgPn.
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite rinst_root in E1, HgPn.
          rewrite rinst_nullable, rinst_root, unify_nullable_nullable.
          exact (ground_unify_without_null env f1 _ _ [] [] HgN HgPn E1).
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H. discriminate H.
      + (* a type variable *)
        destruct HmP as [a Ea]. destruct (Hpb p a Ea) as [_ [o [x [-> _]]]].
        rewrite (rinst_variable p bnd o x Ea). destruct (Hr p o x Ea) as [st' [Hl' Hf']].
        destruct (instance_ground x (proj2 (Hbv p o x Ea))) as [Kx [_ Hgx]].
        apply (rassignee_leaf2 n b p bnd A s s' Hs HA H o _ Hgx).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
    - (* a type argument of a mixed type as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HcP HmP HnP HA Hs Hd H Hr; try contradiction;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      destruct HP as [[Hyt Hot]|[Hot HP]].
      { (* of a type of the arguments: unify takes the two as they are *)
        assert (HnA: no_vars (TypeArgument va oa na) = true).
        { exact (of_fragment_no_vars env declared na (proj1 (proj1 (yfrag_argument env declared caller Qa
              (caller_argument_nested env declared ps) b va oa na HA)))). }
        assert (Hnt: no_vars (TypeArgument vt ot nt) = true) by exact (of_fragment_no_vars env declared nt (proj1 Hyt)).
        destruct (keeps_free env wf (S n) _ _ s s' Hnt HnA H) as [-> H0].
        pose proof (free_closed_argument env declared caller b Hpb vt ot nt Hyt Hot) as Ef.
        rewrite Ef in HcP. unfold rinst. rewrite Ef.
        exact (subst_arguments (S n) _ _ HcP (proj2 (proj2 (proj2 (proj2 HA)))) H0). }
      destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      destruct (proj2 (proj2 (proj2 (proj2 HA)))) as [HcN [Hmq _]].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (gwf2_capturable env declared caller s nt Hs)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      destruct (instance_of_argument va oa na HcN Hmq) as [EA HgN].
      assert (Efree: instantiate_free env b (TypeArgument vt ot nt) = TypeArgument vt ot (instantiate_free env b nt)).
      { rewrite (free_argument env b vt ot nt Hpb (mixed_nested env declared caller b Hpb nt HP)), (free_plain_ownership b ot Hot).
        reflexivity. }
      rewrite Efree in HcP. destruct HcP as [HcNt [Hmt _]].
      destruct (instance_of_argument vt ot (instantiate_free env b nt) HcNt Hmt) as [ET HgT].
      assert (ERT: rinst b (TypeArgument vt ot nt) = TypeArgument vt ot (rinst b nt)).
      { unfold rinst. rewrite Efree, ET. destruct ot; try discriminate Hot; reflexivity. }
      pose proof (ownership_concrete oa ot Hot Ho) as Hown.
      assert (Hfi: is_type_variable (rinst b nt) = false) by exact (gfrag_not_variable env _ (ground_gfrag env _ HgT)).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (rinst b nt) (instantiate env sigma na) [] = Some (Ongoing []) ->
          unify env (S f) (rinst b (TypeArgument vt ot nt)) (instantiate env sigma (TypeArgument va oa na)) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite ERT, EA.
        rewrite (unify_type_arguments env f vt ot (rinst b nt) va _ (instantiate env sigma na) [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (Gt nt na s s1 HP HAn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n nt na s s1 E1) as Hk1. pose proof (dom_forward2 b s s1 Hs Hk1 Hd) as Hd1.
           destruct (Ga nt na s1 s' HP HAn Hs1 H) as [_ [Hm2 _]]. pose proof (unify_keeps_exact env n na nt s1 s' H) as Hk2.
           destruct (IHa nt na s1 s' HP HcNt HmP HnP HAn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHt nt na s s1 HP HcNt HmP HnP HAn Hs Hd E1 (rsat_back2 b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HcNt HmP HnP HAn Hs Hd H Hr) as [f Hf]
          | destruct (IHa nt na s s' HP HcNt HmP HnP HAn Hs Hd H Hr) as [f Hf]
          | destruct (IHt nt top_type s s' HP HcNt HmP HnP (yfrag_top env wf declared caller caller_top' b) Hs Hd H Hr) as [f Hf]
          | destruct (IHa nt bottom_type s s' HP HcNt HmP HnP (yfrag_bottom env wf declared caller caller_bottom' b) Hs Hd H Hr) as [f Hf] ];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument of a mixed type as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HcP HmP HnP HA Hs Hd H Hr; try contradiction;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      destruct HP as [[Hyp Hop]|[Hop HP]].
      { assert (HnA: no_vars (TypeArgument va oa na) = true).
        { exact (of_fragment_no_vars env declared na (proj1 (proj1 (yfrag_argument env declared caller Qa
              (caller_argument_nested env declared ps) b va oa na HA)))). }
        assert (Hnp: no_vars (TypeArgument vp op np) = true) by exact (of_fragment_no_vars env declared np (proj1 Hyp)).
        destruct (keeps_free env wf (S n) _ _ s s' HnA Hnp H) as [-> H0].
        pose proof (free_closed_argument env declared caller b Hpb vp op np Hyp Hop) as Ef.
        rewrite Ef in HcP. unfold rinst. rewrite Ef.
        exact (subst_arguments (S n) _ _ (proj2 (proj2 (proj2 (proj2 HA)))) HcP H0). }
      destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      destruct (proj2 (proj2 (proj2 (proj2 HA)))) as [HcN [Hmq _]].
      rewrite (unify_type_arguments env n va oa na vp op np s (gfrag_not_variable env na (proj1 (proj1 HAn)))) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      destruct (instance_of_argument va oa na HcN Hmq) as [EA HgN].
      assert (Efree: instantiate_free env b (TypeArgument vp op np) = TypeArgument vp op (instantiate_free env b np)).
      { rewrite (free_argument env b vp op np Hpb (mixed_nested env declared caller b Hpb np HP)), (free_plain_ownership b op Hop).
        reflexivity. }
      rewrite Efree in HcP. destruct HcP as [HcNp [Hmp _]].
      destruct (instance_of_argument vp op (instantiate_free env b np) HcNp Hmp) as [EP HgP].
      assert (ERP: rinst b (TypeArgument vp op np) = TypeArgument vp op (rinst b np)).
      { unfold rinst. rewrite Efree, EP. destruct op; try discriminate Hop; reflexivity. }
      pose proof (ownership_concrete_flipped op oa Hop Ho) as Hown.
      assert (Hgoal: forall f, compare_variances (unify env f) va vp (instantiate env sigma na) (rinst b np) [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env sigma (TypeArgument va oa na)) (rinst b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite ERP, EA.
        rewrite (unify_type_arguments env f va _ (instantiate env sigma na) vp op (rinst b np) [] (gfrag_not_variable env _ (ground_gfrag env _ HgN))), Hown.
        exact E. }
      pose proof (of_fragment_no_vars env declared na (proj1 HAn)) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (Ga np na s s1 HP HAn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n na np s s1 E1) as Hk1. pose proof (dom_forward2 b s s1 Hs Hk1 Hd) as Hd1.
           destruct (Gt np na s1 s' HP HAn Hs1 H) as [_ [Hm2 _]]. pose proof (unify_keeps_exact env n np na s1 s' H) as Hk2.
           destruct (IHt np na s1 s' HP HcNp HmP HnP HAn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHa np na s s1 HP HcNp HmP HnP HAn Hs Hd E1 (rsat_back2 b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HcNp HmP HnP HAn Hs Hd H Hr) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HcNp HmP HnP HAn Hs Hd H Hr) as [f Hf];
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

End RuntimeMixed.

(* The types of the parameters mention Nothing only as `exclusive Nothing`, and so do mixed types made
   of them and types of the arguments *)
Lemma ifrag_nib: forall P, ifrag env P = true -> nothing_is_bottom P = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] HS; try discriminate HS; try reflexivity.
    - pose proof (root_args_ifrag env wf m c args HS) as Hargs.
      destruct (ifrag_cases env wf _ HS) as [[m' [c' [args' [Heq [Hcn _]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
          try discriminate Heq.
      + injection Heq as <- <- <-. cbn [nothing_is_bottom]. rewrite Hcn. cbn [andb]. clear Hcn HS.
        induction args as [|a args IHa]; [reflexivity|]. cbn [forallb]. apply andb_true_iff. split.
        * pose proof (Hargs a (or_introl eq_refl)) as Ha. destruct a as [| | | |v o n| |]; try discriminate Ha. exact (IH n Ha).
        * exact (IHa (fun a' Ha' => Hargs a' (or_intror Ha'))).
      + unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity.
    - assert (Hn: ifrag env n = true).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[Heq|[[m [c [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. exact H'. }
      exact (IH n Hn).
Qed.

(* A parameter, also of a type variable made nullable, at run time *)
Lemma runtime_mparameter: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
    forall n P A s s', pfrag env P = true -> no_given P = true -> plain_owners P = true -> vars_in (bound_b b) P = true ->
    yfrag env declared caller b A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    exists f, unify env f (instantiate env sigma (pinstance env (instantiate_free env b) P)) (instantiate env sigma A) (Ongoing [])
        = Some (Ongoing []).
Proof.
    intros b Hpb Hbv n P A s s' HP Hg Ho Hv HA Hs Hd H Hr.
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsr _]]]]]|[gm [nn [p [-> [Hsr _]]]]]]].
    { rewrite (pinstance_ifrag env wf _ P HP').
      exact (proj1 (runtime_mixed b Hpb Hbv n) P A s s' (ifrag_mfrag env wf declared caller b P HP' Ho)
          (free_caller env wf declared ps b Hpb (fun q o x E => proj2 (Hbv q o x E)) P HP' Ho Hv)
          (vars_in_mbinds b P Hv) (ifrag_nib P HP') HA Hs Hd H Hr). }
    all: destruct gm; [discriminate Hg|].
    all: cbn [vars_in] in Hv; rewrite andb_true_r in Hv; unfold bound_b in Hv.
    all: destruct (lookup_binding b p) as [a|] eqn:Ea; [|discriminate Hv].
    all: destruct (Hpb p a Ea) as [Hl [o [x [-> Hy]]]].
    all: assert (Ei: forall nn', instantiate_free env b (TypeVariable (mkGenericRef None nn' p [])) = x)
        by (intros nn'; cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    all: destruct (Hbv p o x Ea) as [Hfx Hcx].
    all: destruct (instance_ground x Hcx) as [_ [_ Hgx]].
    all: destruct (Hr p o x Ea) as [st' [Hl' Hfit]].
    all: assert (Hfits: forall st'', lookup_state s' p = Some st'' -> rfits st'' o (instantiate env sigma x))
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    (* the type the variable stands for, at run time *)
    all: assert (HZ: ground env (instantiate env sigma (if nn then without_null env x else x)) = true
        /\ without_null env (instantiate env sigma (if nn then without_null env x else x)) = without_null env (instantiate env sigma x)
        /\ (nn = true -> is_nullable env (instantiate env sigma (if nn then without_null env x else x)) = false)).
    all: try (destruct nn; [|split; [exact Hgx|split; [reflexivity|intros E; discriminate E]]];
        pose proof (caller_without_null env wf declared ps x Hcx) as Hcw;
        destruct (instance_ground _ Hcw) as [Kw [Hbw HgZ]];
        split; [exact HgZ|]; split;
        [rewrite (without_null_nullable_assignee x (proj1 Hfx)); exact (instance_nullable_assignee x (proj1 Hfx) Hcx)|];
        intros _; exact (proj1 (proj2 (inst_facts env wf sigma Kw Hsf _ (proj1 Hcw) Hbw))
            (without_null_not_nullable env wf declared declared_wf x (proj1 Hfx)))).
    - (* the variable itself, narrowed or not *)
      destruct n as [|n]; [discriminate H|].
      destruct (unify_variable_given env wf n None nn p A s s' (shape_of_fragment A (proj1 (proj1 HA))) H) as [H1 [_ Hnul]].
      destruct (rtarget_leaf2 n b p [] _ s s' Hs HA H1 o _ Hgx Hfits) as [f Hf].
      cbn [pinstance]. rewrite Ei. unfold ref_apply. cbn zeta.
      destruct nn; [|exists f; exact Hf].
      apply (runtime_without_null A _ _ f (proj2 (proj2 (proj2 HA))) Hgx (proj1 HZ) (proj2 (proj2 HZ) eq_refl) (proj1 (proj2 HZ)));
          [|exact Hf].
      destruct (is_nullable env A) eqn:EA; [|reflexivity].
      rewrite (narrowed_not_nullable env wf None p Hsr) in Hnul. discriminate (Hnul eq_refl).
    - (* made nullable: the variable takes the argument without null *)
      destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 (proj1 HA))) as [HgA0 _].
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (unify_variable_given env wf n None nn p _ s s' (shape_of_fragment _ HgA0) H) as [H1 _].
      pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps) b A HA)
          as HA0.
      destruct (rtarget_leaf2 n b p [] _ s s' Hs HA0 H1 o _ Hgx Hfits) as [f Hf].
      cbn [pinstance]. rewrite Ei, rewrap_sigma. unfold ref_apply. cbn zeta.
      exact (runtime_nullable_variable A _ _ f (proj1 (proj1 HA)) (proj2 (proj2 (proj2 HA))) Hgx (proj1 HZ) (proj1 (proj2 HZ)) Hf).
Qed.

Lemma bottom_only_nib: forall t, bottom_only env t = true -> nothing_is_bottom t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [bottom_only] in H; cbn [nothing_is_bottom]; try reflexivity.
    - apply andb_true_iff in H. destruct H as [Hc Ha]. apply andb_true_iff. split; [exact Hc|]. clear Hc.
      induction args as [|a args IHa]; [reflexivity|]. cbn [forallb] in Ha |- *. apply andb_true_iff in Ha. destruct Ha as [Ha Has].
      rewrite (IH a Ha). exact (IHa Has).
    - exact (IH n H).
    - exact (IH n H).
Qed.

Lemma nib_candidate: forall p c, gfrag env c = true -> nothing_is_bottom c = true ->
    forall S, ifrag env S = true -> nothing_is_bottom (with_candidate env p c S) = true.
Proof.
    intros p c Hgc Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c Hgc).
    assert (Hpp: forall q a, lookup_binding [(p, TypeArgument Model.invariant ref c)] q = Some a -> is_loose a = false).
    { intros q a E. cbn [lookup_binding] in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hfinal: final_argument (TypeArgument Model.invariant ref c) = c).
    { unfold final_argument. cbn [is_loose Variance_beq negb orb]. rewrite Hcn. reflexivity. }
    assert (Hshape: forall n, ifrag env n = true -> nests_argument (with_candidate env p c n) = false).
    { intros n Hn. destruct (ifrag_cases env wf n Hn) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          try reflexivity.
      unfold with_candidate. cbn [instantiate lookup_binding]. destruct (param_eqb q p); [rewrite Hfinal; exact Hcn|reflexivity]. }
    fix IH 1. intros [m c' args|n|g|me msg|v o n|[gm nn q vs]|cs] HS; try discriminate HS.
    - pose proof (root_args_ifrag env wf m c' args HS) as Hargs.
      destruct (ifrag_cases env wf _ HS) as [[m' [c'' [args' [Heq [Hcn' _]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
          try discriminate Heq.
      + injection Heq as <- <- <-. unfold with_candidate. cbn [instantiate nothing_is_bottom]. rewrite Hcn'. cbn [andb].
        clear HS Hcn'.
        induction args as [|a args IHa]; [reflexivity|]. cbn [map forallb]. apply andb_true_iff.
        split; [|exact (IHa (fun a' Ha' => Hargs a' (or_intror Ha')))].
        pose proof (Hargs a (or_introl eq_refl)) as Ha. destruct a as [| | | |v o n| |]; try discriminate Ha.
        cbn [argument_ifrag] in Ha. pose proof (Hshape n Ha) as Hns.
        rewrite (instantiate_unloose_argument env _ v o n Hpp).
        * cbn [nothing_is_bottom]. exact (IH n Ha).
        * unfold with_candidate in Hns. destruct (instantiate env _ n) as [| | | | | |]; try reflexivity; discriminate Hns.
        * intros x Ex. unfold with_candidate in Hns. rewrite Ex in Hns. destruct x; try reflexivity; discriminate Hns.
      + unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity.
    - assert (Hn: ifrag env n = true /\ exists m c' args, n = RootResolved m c' args).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[Heq|[[m [c' [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct (Hn) as [Hn' Hroot]. pose proof (IH n Hn') as Hm.
      destruct Hroot as [m [c' [args ->]]].
      unfold with_candidate in Hm |- *. cbn [instantiate] in Hm |- *. cbn [rewrap_nullable nothing_is_bottom]. exact Hm.
    - unfold ifrag in HS. cbn [no_generics] in HS. rewrite andb_false_r in HS. discriminate HS.
    - destruct gm, nn; try (unfold ifrag in HS; apply andb_true_iff in HS; destruct HS as [_ HS]; discriminate HS).
      unfold with_candidate. cbn [instantiate lookup_binding]. destruct (param_eqb q p); [rewrite Hfinal; exact Hnc|reflexivity].
Qed.

(* The lower bound of p, checked against its static upper bound with type variables at run time: for
   bindings of variables to types of generic code that the states stand for at run time (rsat2), not
   of the ownerships of the lower bound, it is below the static upper bound with p bound to it,
   instantiated *)
Definition rstatic_checked (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    is_non_nullable_nothing env (lower_bound st) = false -> no_vars (static_upper_bound st) = false ->
    forall b, plain_values b ->
        (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
        dom b s -> owners_free env b (lower_bound st) -> vars_in (fun q => param_eqb q p || bound_b b q) (static_upper_bound st) = true ->
        rsat2 b s -> forall C, In C (bound_components (static_upper_bound st)) ->
        exists f, unify env f (rinst b (with_candidate env p (lower_bound st) C))
            (instantiate env sigma (lower_bound st)) (Ongoing []) = Some (Ongoing []).

(* The variable states inference works with, for receivers of generic code: as gwf2, the lower bounds
   checked at run time *)
Definition gw3 (s: VariableStates): Prop :=
    gw s /\ forall p st, lookup_state s p = Some st -> is_exact st = false -> rstatic_checked s p st.

Lemma gw3_capturable: forall s t, gw3 s -> capturable t s = None.
Proof. intros s t Hs. exact (gwf2_capturable env declared caller s t (proj1 Hs)). Qed.

(* Unify adds no variables: those bound in b had states before *)
Lemma dom_back: forall b s s', keeps_exact s s' -> dom b s' -> dom b s.
Proof. intros b s s' Hk Hd p o z Hp. destruct (Hd p o z Hp) as [st' Hl']. exact (keeps_exact_domain s s' p st' Hk Hl'). Qed.

Lemma rstatic_mono: forall s s' p st,
    (forall b, dom b s' -> rsat2 b s' -> dom b s /\ rsat2 b s) ->
    rstatic_checked s p st -> rstatic_checked s' p st.
Proof.
    intros s s' p st Hm H Hnn Hnv b Hpb Hbv Hd Ho Hv Hr. destruct (Hm b Hd Hr) as [Hd' Hr'].
    exact (H Hnn Hnv b Hpb Hbv Hd' Ho Hv Hr').
Qed.

Let gwhole := gstatic_whole env wf declared declared_wf terminates finite not_expansive caller Qa
    (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
    (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
    (caller_component env declared ps) (caller_supertype_arguments env wf declared ps).

(*
 * The static check of a candidate c against a static upper bound with type variables, at run time:
 * for bindings of the variables to types of generic code that the states the check ends with stand
 * for at run time, c, instantiated, is below each component of the bound with c in place of p. As
 * GenericArguments.gstatic_whole: the components that aren't type variables by runtime_mixed, those
 * that are by what they take (rtarget_leaf2).
 *)
(* The static check of a candidate c against an intersection that is its static upper bound, of the
   assignee a, at run time: as gstatic_components *)
Lemma rstatic_components: forall n p cs c a s s',
    (forall C, In C cs -> ifrag env C = true /\ plain_owners C = true /\ forall g, C = TypeVariable g -> param_of g <> p) ->
    components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    of_fragment env declared c -> bottom_only env c = true -> caller c ->
    (forall b, owners_free env b c -> yfrag env declared caller b a) -> gw s ->
    unify env n (with_candidate env p c (Intersection cs)) a (Ongoing s) = Some (Ongoing s') ->
    forall b, plain_values b ->
        (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
        owners_free env b c -> vars_in (fun q => param_eqb q p || bound_b b q) (Intersection cs) = true -> dom b s -> rsat2 b s' ->
        forall C, In C cs ->
        exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p cs c a s s' Hcomp Hcs Hunif Hc Hbc Hqc Hya Hs H b Hpb Hbv Hob Hvb Hd Hr.
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x)
        by (intros q o x E; exact (proj1 (Hbv q o x E))).
    assert (Hycb: yfrag env declared caller b c) by (split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars env declared c Hc) as Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c (proj1 Hc)).
    pose proof (Hya b Hob) as Hyab. destruct Hyab as [Ha [Hba [Hoa Hqa]]]. pose proof (Hya b Hob) as Hyab.
    (* a component that is a type of the parameters, with c in place of p: mixed, its instance of generic code *)
    assert (Hone: forall C, ifrag env C = true -> plain_owners C = true -> (forall g, C = TypeVariable g -> param_of g <> p) ->
        vars_in (fun q => param_eqb q p || bound_b b q) C = true ->
        mfrag env declared caller b (with_candidate env p c C) /\ caller (instantiate_free env b (with_candidate env p c C))
        /\ mbinds b (with_candidate env p c C) /\ nothing_is_bottom (with_candidate env p c C) = true).
    { intros C HCi HCo HCt HvC.
      split; [exact (mfrag_candidate env wf declared caller b p c Hycb C HCi HCo HCt)|].
      split; [|split; [exact (mbinds_candidate env wf b p c C HvC Hnc)|exact (nib_candidate p c (proj1 Hc) (bottom_only_nib c Hbc) C HCi)]].
      rewrite (free_candidate env b p c C Hpb (proj1 Hc) (unmentioned env b c (proj1 Hc) Hob) (ifrag_plain_variables env wf C HCi HCo)).
      apply (free_caller env wf declared ps (with_value p c b)); [| |exact HCi|exact HCo|].
      - intros q a0 Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
        + injection Ea as <-. split; [reflexivity|]. exists ref, c. split; [reflexivity|exact Hcn].
        + exact (Hpb q a0 Ea).
      - intros q o x Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
        + injection Ea as _ <-. exact Hqc.
        + exact (proj2 (Hbv q o x Ea)).
      - apply (vars_in_mono (fun q => param_eqb q p || bound_b b q)); [|exact HvC].
        intros q Ea. unfold bound_b. cbn [with_value lookup_binding]. destruct (param_eqb q p); [reflexivity|exact Ea]. }
    assert (Hvcs: forall C, In C cs -> vars_in (fun q => param_eqb q p || bound_b b q) C = true)
        by (intros C HC; cbn [vars_in] in Hvb; rewrite forallb_forall in Hvb; exact (Hvb C HC)).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    assert (HSi: forall C, In C cs -> ifrag env C = true) by (intros C HC; exact (proj1 (Hcomp C HC))).
    assert (Hnp: forall g, In (TypeVariable g) cs -> param_of g <> p)
        by (intros g Hg; exact (proj2 (proj2 (Hcomp _ Hg)) g eq_refl)).
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists q, C = TypeVariable (mkGenericRef None false q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases env wf p cs C HSi Hcs Hnp HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[q [-> _]]]; [reflexivity|exact Hsh]. }
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    set (m0 := assignment_mutability env (Intersection cs)) in *.
    set (w := fun C => with_mutability env m0 (with_candidate env p c C)) in H.
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists cn, a = Nullable cn).
    { destruct (gfrag_cases env a (proj1 Ha)) as [[? [? [? ->]]]|[[cn [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[cn Ecn]].
    2:{ subst a. rewrite unify_step_once in H. unfold unify_step, unify_intersection in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body env _ _ _ a s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) (map w cs)) in H.
    set (vs := filter is_type_variable (map w cs)) in H.
    destruct (instance_ground a Hqa) as [Kc [_ HgC]].
    (* the components that aren't type variables: the candidate in the bound, at run time *)
    assert (Hroot: forall C, In C cs -> is_type_variable (w C) = false -> forall s0 s0', gw s0 -> dom b s0 ->
        unify env n1 (w C) a (Ongoing s0) = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma a) (Ongoing [])
            = Some (Ongoing []))).
    { intros C HC Hv s0 s0' Hs0 Hd0 E0. destruct (Hcase C HC) as [[m [cl [args EC]]]|[q [EC Hq]]].
      2:{ unfold w in Hv. rewrite EC, (candidate_other env p _ q Hq) in Hv. discriminate Hv. }
      assert (Ew: unify env n1 (w C) a (Ongoing s0) = unify env n1 (with_candidate env p c C) a (Ongoing s0)).
      { pose proof (Hunif C HC) as Hu. unfold w. rewrite EC in Hu |- *. unfold with_candidate.
        cbn [instantiate with_mutability]. apply (unify_root_mutability_any env wf declared declared_wf); [exact (proj1 Ha)|].
        cbn [assignment_mutability] in Hu |- *. destruct (is_const (declaration_of env cl)); [reflexivity|exact (eq_sym Hu)]. }
      rewrite Ew in E0. destruct (Hcomp C HC) as [HCi [HCo HCt]]. destruct (Hone C HCi HCo HCt (Hvcs C HC)) as [HmC [HcC [HbC HnC]]].
      destruct (proj1 (mixed_arguments env wf declared declared_wf terminates finite not_expansive caller Qa
          (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b Hpb Hbf
          gw (gwf2_capturable env declared caller) n1 (fun k _ => gleaf k b))
          _ a s0 s0' HmC Hyab Hs0 E0) as [Hs0' [Hn0 _]].
      split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact (unify_keeps_exact env n1 _ a s0 s0' E0)|].
      intros Hr0. exact (proj1 (runtime_mixed b Hpb Hbv n1) _ a s0 s0' HmC HcC HbC HnC Hyab Hs0 Hd0 E0 Hr0). }
    destruct (fold_unify (fun inner component => unify env n1 component a inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (rfold2 b (fun x inner => unify env n1 x a inner)
        (fun x => forall C, In C cs -> w C = x ->
            exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))
        ns s s2) as [Hs2 [Hd2 [_ [_ Hall2]]]].
    { intros x. apply unify_keeps_failure. }
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      apply in_map_iff in Hx. destruct Hx as [C0 [<- HC0]].
      destruct (Hroot C0 HC0 Hv s0 s0' Hs0 Hd0 E0) as [Hs0' [Hn0 [Hk0 _]]].
      split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact Hk0|].
      intros Hr0 C HC Ew. rewrite <- Ew in Hv, E0. exact (proj2 (proj2 (proj2 (Hroot C HC Hv s0 s0' Hs0 Hd0 E0))) Hr0). }
    { exact Hs. }
    { exact Hd. }
    { exact E2. }
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, gw s3 /\ keeps_exact s2 s3 /\ (forall b', gsatisfies env declared b' s3 -> gsatisfies env declared b' s2)
        /\ of_fragment env declared na /\ bottom_only env na = true /\ caller na /\ owners_free env b na /\ below env a na
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component a inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component a (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of c, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        apply in_map_iff in Hcov. destruct Hcov as [C1 [EC1 HC1]].
        assert (Ecov1: unify env n1 (w C1) a (Ongoing s2) = Some (Ongoing s3)) by (rewrite EC1; exact Ecov).
        destruct (Hroot C1 HC1 ltac:(rewrite EC1; exact Hv) s2 s3 Hs2 Hd2 Ecov1) as [Hs3 [Hn3 [Hk3 _]]].
        destruct (Hcase C1 HC1) as [[m1 [cl1 [args1 EC]]]|[q [EC Hq]]].
        2:{ subst cov. unfold w in Hv. rewrite EC, (candidate_other env p _ q Hq) in Hv. discriminate Hv. }
        assert (Ecov': exists mc argsc, cov = RootResolved mc cl1 argsc).
        { subst cov. unfold w. rewrite EC. unfold with_candidate. cbn [instantiate with_mutability]. eauto. }
        destruct Ecov' as [mc [argsc ->]].
        destruct (root_takes env wf declared declared_wf n1 mc cl1 argsc a s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn', andb_false_r in H.
        set (m' := intersect_mutability (mutability_of env a) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hk3|]. split; [exact Hn3|]. split; [exact (any_of_fragment env wf declared m')|].
        split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
        split; [exact (caller_any env wf declared ps m')|]. split; [exact I|]. split; [|exact H].
        apply (below_any_of env wf declared declared_wf terminates finite not_expansive); [exact Ha|exact Hcn'|].
        unfold m'. apply intersect_mutability_greatest.
        + exact (assignment_mutability_below env ranked a).
        + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)).
      - (* nothing covers: the variables take c *)
        exists a, s2. split; [exact Hs2|]. split; [apply keeps_exact_refl|]. split; [auto|]. split; [exact Ha|].
        split; [exact Hba|]. split; [exact Hqa|]. split; [exact Hoa|].
        split; [exact (below_refl env wf declared declared_wf terminates finite not_expansive a Ha)|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hk3 [Hn3 [Hfna [Hbna [Hqna [Hona [Hcna Hfold]]]]]]]]]].
    assert (Hyna: yfrag env declared caller b na) by (split; [exact Hfna|]; split; [exact Hbna|]; split; [exact Hona|exact Hqna]).
    destruct (instance_ground na Hqna) as [Kn [_ HgNa]].
    (* the type variables among the components: what they take, c is below, at run time *)
    assert (Hvs: forall x, In x vs -> forall s0 s0', gw s0 -> dom b s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x a (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> forall q, x = TypeVariable (mkGenericRef (Some m0) false q []) -> forall o y,
            lookup_binding b q = Some (TypeArgument Model.invariant o y) ->
            exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      apply in_map_iff in Hx. destruct Hx as [C0 [EC0 HC0]].
      destruct (Hcase C0 HC0) as [[m [cl [args EC]]]|[q [EC Hq]]].
      { subst x. unfold w in Hv. rewrite EC in Hv. unfold with_candidate in Hv. cbn in Hv. discriminate Hv. }
      assert (Ex: x = TypeVariable (mkGenericRef (Some m0) false q [])).
      { subst x. unfold w. rewrite EC, (candidate_other env p _ q Hq). reflexivity. }
      rewrite Ex in E0 |- *. destruct n1 as [|n2]; [discriminate E0|].
      assert (Hone': forall A, yfrag env declared caller b A ->
          (forall z, ground env z = true -> (exists f, unify env f z (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])) ->
              exists f, unify env f z (instantiate env sigma a) (Ongoing []) = Some (Ongoing [])) ->
          unify env (S n2) (TypeVariable (mkGenericRef (Some m0) false q [])) A (Ongoing s0) = Some (Ongoing s0') ->
          gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
          /\ (rsat2 b s0' -> forall q', TypeVariable (mkGenericRef (Some m0) false q []) = TypeVariable (mkGenericRef (Some m0) false q' []) ->
              forall o y, lookup_binding b q' = Some (TypeArgument Model.invariant o y) ->
              exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))).
      { intros A HA Hthr EA. pose proof (unify_keeps_exact env (S n2) _ A s0 s0' EA) as Hk0.
        apply (variable_mutability_given env wf n2 m0 q A s0 s0' (proj1 (proj1 HA))) in EA.
        destruct (proj1 (gleaf n2 b) q [] A s0 s0' Hs0 HA EA) as [Hs0' [Hn0 _]].
        split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact Hk0|].
        intros Hr0 q' Eq o y Ey. injection Eq as <-.
        destruct (Hr0 q o y Ey) as [st' [Hl' Hf']].
        destruct (instance_ground y (proj2 (Hbv q o y Ey))) as [Ky [_ Hgy]].
        apply (Hthr _ Hgy). apply (rtarget_leaf2 n2 b q [] A s0 s0' Hs0 HA EA o _ Hgy).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'. }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef (Some m0) false q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena;
          try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. apply (Hone' na Hyna); [|exact Ena].
        intros z Hz [f1 E1]. destruct (subst_below a na Hqa Hqna Hcna) as [f2 E2'].
        exact (rtrans _ _ _ HgC HgNa Hz (ex_intro _ f2 E2') (ex_intro _ f1 E1)).
      - exact (Hone' a Hyab (fun z _ E => E) E0). }
    destruct (rfold2 b (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x a inner | r => r end)
        (fun x => forall q, x = TypeVariable (mkGenericRef (Some m0) false q []) -> forall o y,
            lookup_binding b q = Some (TypeArgument Model.invariant o y) ->
            exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))
        vs s3 s') as [_ [_ [Hback3 [_ Hallv]]]].
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    { intros x Hx s0 s0' Hs0 Hd0 E0. exact (Hvs x Hx s0 s0' Hs0 Hd0 E0). }
    { exact Hs3. }
    { exact (dom_forward2 b s2 s3 Hs2 Hk3 Hd2). }
    { exact Hfold. }
    pose proof (Hback3 Hr) as Hr3.
    pose proof (rsat_back2 b s2 s3 Hs2 Hk3 Hn3 Hd2 Hr3) as Hr2.
    intros C HC. destruct (Hcase C HC) as [[m [cl [args EC]]]|[q [EC Hq]]].
    - (* a class type *)
      assert (Hv: is_type_variable (w C) = false) by (unfold w; rewrite EC; reflexivity).
      assert (Hin: In (w C) ns) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Hv; reflexivity]).
      exact (Hall2 Hr2 (w C) Hin C HC eq_refl).
    - (* a type variable *)
      assert (Ew: w C = TypeVariable (mkGenericRef (Some m0) false q []))
          by (unfold w; rewrite EC, (candidate_other env p _ q Hq); reflexivity).
      assert (Hin: In (w C) vs) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Ew; reflexivity]).
      pose proof (Hvcs C HC) as HvC.
      rewrite EC, (candidate_other env p _ q Hq).
      rewrite EC in HvC. cbn [vars_in] in HvC. apply andb_true_iff in HvC. destruct HvC as [Hq' _].
      unfold param_eqb in Hq'. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hq'. cbn [orb] in Hq'. unfold bound_b in Hq'.
      destruct (lookup_binding b q) as [ab|] eqn:Ea; [|discriminate Hq'].
      destruct (Hpb q ab Ea) as [_ [o [y [-> _]]]].
      rewrite (rinst_variable b Hpb q [] o y Ea).
      exact (Hallv Hr (w C) Hin q Ew o y Ea).
Qed.

Lemma rstatic_whole: forall n p S c s s', gstatic_form env p S ->
    of_fragment env declared c -> bottom_only env c = true -> caller c -> gw s ->
    unify env n (with_candidate env p c S) c (Ongoing s) = Some (Ongoing s') ->
    forall b, plain_values b ->
        (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
        owners_free env b c -> vars_in (fun q => param_eqb q p || bound_b b q) S = true -> dom b s -> rsat2 b s' ->
        forall C, In C (bound_components S) ->
        exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma c) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p S c s s' [Hcomp Hinter] Hc Hbc Hqc Hs H b Hpb Hbv Hob Hvb Hd Hr.
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x)
        by (intros q o x E; exact (proj1 (Hbv q o x E))).
    assert (Hycb: yfrag env declared caller b c) by (split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars env declared c Hc) as Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c (proj1 Hc)).
    (* a component that is a type of the parameters, with c in place of p: mixed, its instance of generic code *)
    assert (Hone: forall C, ifrag env C = true -> plain_owners C = true -> (forall g, C = TypeVariable g -> param_of g <> p) ->
        vars_in (fun q => param_eqb q p || bound_b b q) C = true ->
        mfrag env declared caller b (with_candidate env p c C) /\ caller (instantiate_free env b (with_candidate env p c C))
        /\ mbinds b (with_candidate env p c C) /\ nothing_is_bottom (with_candidate env p c C) = true).
    { intros C HCi HCo HCt HvC.
      split; [exact (mfrag_candidate env wf declared caller b p c Hycb C HCi HCo HCt)|].
      split; [|split; [exact (mbinds_candidate env wf b p c C HvC Hnc)|exact (nib_candidate p c (proj1 Hc) (bottom_only_nib c Hbc) C HCi)]].
      rewrite (free_candidate env b p c C Hpb (proj1 Hc) (unmentioned env b c (proj1 Hc) Hob) (ifrag_plain_variables env wf C HCi HCo)).
      apply (free_caller env wf declared ps (with_value p c b)); [| |exact HCi|exact HCo|].
      - intros q a0 Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
        + injection Ea as <-. split; [reflexivity|]. exists ref, c. split; [reflexivity|exact Hcn].
        + exact (Hpb q a0 Ea).
      - intros q o x Ea. cbn [with_value lookup_binding] in Ea. destruct (param_eqb q p).
        + injection Ea as _ <-. exact Hqc.
        + exact (proj2 (Hbv q o x Ea)).
      - apply (vars_in_mono (fun q => param_eqb q p || bound_b b q)); [|exact HvC].
        intros q Ea. unfold bound_b. cbn [with_value lookup_binding]. destruct (param_eqb q p); [reflexivity|exact Ea]. }
    assert (Hcases: bound_components S = [S] \/ (exists cs, S = Intersection cs) \/ (exists cs, S = Nullable (Intersection cs)))
        by (destruct S as [m c' args|[| | | | | |cs]|g|me msg|v o x|g|cs];
            first [left; reflexivity|right; left; exists cs; reflexivity|right; right; exists cs; reflexivity]).
    destruct Hcases as [E|[[cs ->]|[cs ->]]].
    { (* no intersection: as any other type of the parameters *)
      rewrite E. intros C [<-|[]]. rewrite E in Hcomp. destruct (Hcomp S (or_introl eq_refl)) as [HCi [HCo HCt]].
      destruct (Hone S HCi HCo HCt Hvb) as [HmC [HcC [HbC HnC]]].
      exact (proj1 (runtime_mixed b Hpb Hbv n) _ c s s' HmC HcC HbC HnC Hycb Hs Hd H Hr). }
    { destruct (Hinter cs eq_refl) as [Hcs Hunif]. cbn [bound_components] in Hcomp |- *.
      exact (rstatic_components n p cs c c s s' Hcomp Hcs Hunif Hc Hbc Hqc
          (fun b' Hob' => conj Hc (conj Hbc (conj Hob' Hqc))) Hs H b Hpb Hbv Hob Hvb Hd Hr). }
    (* a nullable intersection, of class types: of the candidate without null, the components made nullable *)
    destruct (Hinter cs eq_refl) as [Hcs Hunif]. cbn [bound_components] in Hcomp |- *.
    assert (Hcomp': forall C, In C cs -> (ifrag env C = true /\ plain_owners C = true /\ forall g, C = TypeVariable g -> param_of g <> p)
        /\ exists m cl args, C = RootResolved m cl args).
    { intros C HC. destruct (Hcomp _ (in_map Nullable _ _ HC)) as [HCi [HCo _]].
      destruct (ifrag_cases env wf _ HCi) as [[? [? [? [Eq _]]]]|[Eq|[[m [cl [args [Eq H']]]]|[? [Eq _]]]]]; try discriminate Eq.
      injection Eq as ->. split; [|eauto]. split; [exact H'|]. split; [exact HCo|]. intros g Eg; discriminate Eg. }
    destruct (components_sfrag_facts env _ Hcs) as [Hlen _]. rewrite length_map in Hlen.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists q, C = TypeVariable (mkGenericRef None false q []) /\ q <> p))
        by (intros C HC; left; exact (proj2 (Hcomp' C HC))).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false)
        by (intros C HC; destruct (proj2 (Hcomp' C HC)) as [m [cl [args ->]]]; reflexivity).
    change (with_candidate env p c (Nullable (Intersection cs))) with (rewrap_nullable (with_candidate env p c (Intersection cs))) in H.
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H. cbn [rewrap_nullable] in H.
    destruct n as [|n]; [discriminate H|].
    rewrite (nullable_target env n _ c s (proj1 Hc)) in H. rewrite <- (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    intros C' HC'. apply in_map_iff in HC'. destruct HC' as [C [<- HC]].
    destruct (Hcomp' C HC) as [[HCi [HCo HCt]] _].
    destruct (rstatic_components n p cs c (nullable_assignee env c) s s' (fun C HC => proj1 (Hcomp' C HC)) Hcs Hunif Hc Hbc Hqc
        (fun b' Hob' => yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps)
            b' c (conj Hc (conj Hbc (conj Hob' Hqc)))) Hs H b Hpb Hbv Hob Hvb Hd Hr C HC) as [f Hf].
    assert (HvC: vars_in (fun q => param_eqb q p || bound_b b q) C = true)
        by (cbn [vars_in] in Hvb; rewrite forallb_forall in Hvb; exact (Hvb C HC)).
    destruct (Hone C HCi HCo HCt HvC) as [_ [HcC _]]. destruct (instance_ground _ HcC) as [_ [_ HgZ]].
    unfold rinst. change (with_candidate env p c (Nullable C)) with (rewrap_nullable (with_candidate env p c C)).
    rewrite (free_rewrap env b), rewrap_sigma.
    exact (runtime_nullable_variable c _ _ f (proj1 Hc) Hqc HgZ HgZ eq_refl Hf).
Qed.

(*
 * What unify does with a type variable keeps the states of gw3: as gleaf_all, and a new lower bound,
 * checked against a static upper bound with type variables, is so at run time (runtime_mixed).
 *)
Lemma rleaf_all: forall n b, mleaf env declared caller b gw3 n.
Proof.
    induction n as [n IHn] using lt_wf_ind. intros b0.
    assert (Hback: forall s s', gw s -> keeps_exact s s' -> (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s) ->
        forall b, dom b s' -> rsat2 b s' -> dom b s /\ rsat2 b s).
    { intros s s' Hs Hk Hm b Hd Hr. pose proof (dom_back b s s' Hk Hd) as Hd0. exact (conj Hd0 (rsat_back2 b s s' Hs Hk Hm Hd0 Hr)). }
    split.
    - (* the variable is the target *)
      intros p bnd A s s' [Hs Hc] HA H.
      destruct (proj1 (gleaf n b0) p bnd A s s' Hs HA H) as [Hs' [Hext Hsnd]].
      pose proof (unify_keeps_exact env (S n) _ A s s' H) as Hk.
      split; [|split; [exact Hext|exact Hsnd]].
      split; [exact Hs'|].
      pose proof (variable_target_step env n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
      unfold plus_supertype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
      destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
      destruct (is_exact st) eqn:Ee.
      + destruct (keeps_free env wf n _ A s s' Hnl (of_fragment_no_vars env declared A (proj1 HA)) H') as [-> _]. exact Hc.
      + cbn zeta in H'.
        destruct (He eq_refl) as [Hcap [Hlu [Hbu [Hbl [Hqu [Hql [Hbo Hok]]]]]]].
        pose proof (supertype_of_fragment env declared supertype_in_fragment _ _ Hbl (proj1 HA)) as Hfs.
        destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
            as [[ns|]|] eqn:E; try discriminate H'.
        destruct (keeps_free env wf n _ _ s ns Hnu (of_fragment_no_vars env declared _ Hfs) E) as [-> _].
        destruct (below_supertype env wf declared supertype_in_fragment supertype_above _ _ Hbl (proj1 HA)) as [Hlo _].
        pose proof (supertype_generic ps _ _ Hbl (proj1 HA) Hql (proj2 (proj2 (proj2 HA)))) as Hqc.
        pose proof (supertype_bottom_only _ _ Hbl (proj1 HA) Hbo (proj1 (proj2 HA))) as Hbc.
        set (c := closest_common_supertype_with env (lower_bound st) A) in *.
        pose proof (of_fragment_no_vars env declared c Hfs) as Hnc.
        set (st' := mkVariableState (static_upper_bound st) (upper_bound st) c false (is_capturable st)).
        destruct (plus_static_check env (unify env n) st p c (Ongoing s)) as [[s2|]|] eqn:E2; cbn beta iota in H'; try discriminate H'.
        injection H' as <-.
        (* the check: the states it ends with, p as it was *)
        assert (Hchk: gw3 s2 /\ lookup_state s2 p = Some st
            /\ (no_vars (static_upper_bound st) = false ->
                unify env n (with_candidate env p c (static_upper_bound st)) c (Ongoing s) = Some (Ongoing s2))).
        { unfold plus_static_check in E2. destruct (no_vars (static_upper_bound st)) eqn:Ens.
          - injection E2 as <-. split; [exact (conj Hs Hc)|]. split; [exact Hl|]. intros E'; discriminate E'.
          - unfold gstatic_ok in Hok. rewrite Ens in Hok. destruct Hok as [Hform _].
            destruct (gwhole gw3 gw3_capturable n p _ c s s2 IHn Hform Hfs Hbc Hqc (conj Hs Hc) E2) as [Hs2 _].
            destruct (unify_keeps_from env wf intersect_no_vars supertype_no_vars n (parameter_rank env p) _ c s s2
                (gwf2_ranked env declared caller s Hs)
                (or_intror (conj (candidate_below env wf p c _ Hsv Hnc) Hnc)) E2) as [Kf _].
            split; [exact Hs2|]. split; [rewrite (Kf p (le_n _)); exact Hl|]. intros _. exact E2. }
        destruct Hchk as [[Hs2 Hc2] [Hl2 Echk]].
        assert (Hfit': forall o x, of_fragment env declared x -> gfits env declared st' o x -> gfits env declared st o x).
        { intros o x Hx Hfit. unfold gfits in Hfit |- *. rewrite Ee. unfold st' in Hfit. cbn [is_exact upper_bound lower_bound] in Hfit.
          destruct Hfit as [E1' E2']. split; [|exact E2'].
          exact (below_trans env wf declared declared_wf terminates finite not_expansive _ _ x Hbl Hfs Hx Hlo E1'). }
        assert (Hr2: forall b, rsat2 b (set_state s2 p st') -> rsat2 b s2).
        { intros b Hr q o x Hq. destruct (Hr q o x Hq) as [st0 [Hl0 Hf0]]. destruct (Nat.eq_dec p q) as [<-|Hne].
          - rewrite lookup_set_same in Hl0. injection Hl0 as <-. exists st. split; [exact Hl2|].
            unfold rfits in Hf0 |- *. unfold st' in Hf0. cbn [is_exact] in Hf0. rewrite Ee.
            destruct Hf0 as [x' [Hx' [Hcx [Hg Ez]]]]. exists x'. split; [exact Hx'|]. split; [exact Hcx|]. split; [|exact Ez].
            exact (Hfit' o x' Hx' Hg).
          - rewrite lookup_set_other in Hl0 by exact Hne. exists st0. split; [exact Hl0|exact Hf0]. }
        intros q st0 Hq0 Eq0. destruct (Nat.eq_dec p q) as [<-|Hne].
        * (* the new lower bound, checked at run time *)
          rewrite lookup_set_same in Hq0. injection Hq0 as <-.
          intros Hnn Hnv b Hpb Hbv Hbd Ho Hv Hr.
          unfold st' in Hnn, Hnv, Ho, Hv |- *. cbn [lower_bound static_upper_bound] in Hnn, Hnv, Ho, Hv |- *.
          unfold gstatic_ok in Hok. rewrite Hnv in Hok. destruct Hok as [Hform _].
          exact (rstatic_whole n p _ c s s2 Hform Hfs Hbc Hqc Hs (Echk Hnv) b Hpb Hbv Ho Hv (dom_back b s _ Hk Hbd) (Hr2 b Hr)).
        * rewrite lookup_set_other in Hq0 by exact Hne.
          apply (rstatic_mono s2 _ q st0); [|exact (Hc2 q st0 Hq0 Eq0)].
          intros b Hd' Hr. split; [|exact (Hr2 b Hr)].
          intros q' o x Hq'. destruct (Hd' q' o x Hq') as [st1 Hl1]. destruct (Nat.eq_dec p q') as [<-|Hne'].
          -- exists st. exact Hl2.
          -- rewrite lookup_set_other in Hl1 by exact Hne'. exists st1. exact Hl1.
    - (* the variable is the assignee *)
      intros p bnd A s s' [Hs Hc] HA H.
      destruct (proj2 (gleaf n b0) p bnd A s s' Hs HA H) as [Hs' [Hext Hsnd]].
      pose proof (unify_keeps_exact env (S n) A _ s s' H) as Hk.
      split; [|split; [exact Hext|exact Hsnd]].
      split; [exact Hs'|].
      pose proof (variable_assignee_step env n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
      unfold plus_subtype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
      destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
      destruct (is_exact st) eqn:Ee.
      + destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars env declared A (proj1 HA)) Hnu H') as [-> _]. exact Hc.
      + cbn zeta in H'.
        destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
        destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s)) as [[ns|]|] eqn:E; try discriminate H'.
        destruct (keeps_free env wf n _ _ s ns (intersect_no_vars _ _ Hnu (of_fragment_no_vars env declared A (proj1 HA))) Hnl E)
            as [-> _].
        injection H' as <-.
        (* the lower bound stays *)
        intros q st0 Hq0 Eq0. destruct (Nat.eq_dec p q) as [<-|Hne].
        * rewrite lookup_set_same in Hq0. injection Hq0 as <-.
          exact (rstatic_mono s _ p st (Hback s _ Hs Hk Hext) (Hc p st Hl Ee)).
        * rewrite lookup_set_other in Hq0 by exact Hne.
          exact (rstatic_mono s _ q st0 (Hback s _ Hs Hk Hext) (Hc q st0 Hq0 Eq0)).
Qed.

(*
 * Calling a member function whose type parameters are bounded by types mentioning them, on a receiver
 * of generic code, is sound at run time: as member_call_on_generic_receiver, with the static upper
 * bounds of generic_member_call_with_bounded_variables_sound. The type parameters of the class stand
 * for the type arguments of the object as that class, those of the function for their final values,
 * instantiated (rinst): the final values are within their static upper bounds so bound, and each
 * argument fits its parameter so bound, at run time. The type parameters of the caller are none of
 * those of the callee.
 *)
Theorem generic_receiver_with_bounded_variables_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p S, In (p, S) cvars -> in_fragment env S = true) ->
    (forall p S, In (p, S) ovars -> gstatic_bound env declared caller (cvars ++ ovars) p S) ->
    (forall q, In q ps -> ~ In q (map fst (cvars ++ ovars))) ->
    (* the receiver, of generic code, unified with the receiver parameter *)
    of_fragment env declared (RootResolved ma ca ys) -> caller (RootResolved ma ca ys) ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is at run time, below the receiver instantiated; its type arguments exact *)
    in_fragment env (RootResolved mo e xs) = true -> nothing_is_bottom (RootResolved mo e xs) = true ->
    closed (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (instantiate env sigma (RootResolved ma ca ys)) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (* the parameters, and the arguments of generic code, accepted in turn *)
    (forall P, In P Ps -> pfrag env P = true /\ plain_owners P = true
        /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (forall P, In P Ps -> no_given P = true) ->
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ caller A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of env U (fst v)))) ovars ->
    (forall p S, In (p, S) ovars -> forall C, In C (bound_components S) ->
        exists f, unify env f (rinst b C) (instantiate env sigma (gfinal_of env U p)) (Ongoing []) = Some (Ongoing []))
    /\ forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (pinstance env (instantiate_free env b) P)) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hcb Hst Hdis HfR HcR Hrec
        Hfo Hno Hcl Hobj Hzs Hxx HPs HPg HAs Hfold Hlow b Hbdef.
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) (map fst cvars)))) vars).
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
    assert (Hfresh: forall p bound, In (p, bound) cvars -> lookup_state s0 p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)).
    { intros p bound Hin. unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin).
      reflexivity. }
    destruct (gcapture_arguments n cvars ys' s0 u Hndc Hl (fun y Hy => proj1 (Hys y Hy))
        (fun p bound Hin => in_fragment_no_vars env bound (Hcb p bound Hin)) Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variable states unify works with *)
    assert (Hu: forall p st, lookup_state u p = Some st ->
        (exists i bound y, nth_error cvars i = Some (p, bound) /\ nth_error ys' i = Some y /\ st = mkVariableState bound y y true true)
        \/ (exists bound, In (p, bound) ovars /\ st = mkVariableState bound (initial_upper_bound bound) bottom_type false false)).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
      - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        rewrite (Hcap i p bound y Hi Hy) in Hp. injection Hp as <-. left. exists i, bound, y. auto.
      - pose proof Hp as Hp2. rewrite (Hoth p Hnin) in Hp2. unfold s0 in Hp2. destruct (lookup_for_inference_in _ _ p st Hp2) as [bound Hin].
        apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin)|].
        right. exists bound. split; [exact Hin|]. rewrite (Hownu p bound Hin) in Hp. injection Hp as <-. reflexivity. }
    (* the states after the receiver: the type parameters of c captured, those of the function as they start *)
    assert (Hwfu: gw3 u).
    { split.
      - intros p st Hp. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]].
        + unfold gstate_ok. cbn [upper_bound lower_bound is_exact static_upper_bound].
          pose proof (argument_gfrag_no_vars env y (proj1 (Hys y (nth_error_In _ _ Hy)))) as Hny.
          split; [exact Hny|]. split; [exact Hny|]. split; [intros E; discriminate E|].
          exact (no_vars_in _ _ (in_fragment_no_vars env bound (Hcb p bound (nth_error_In _ _ Hi)))).
        + exact (ginitial_ok env wf declared declared_wf terminates finite not_expansive caller caller_top' caller_bottom'
              vars p bound u (Hst p bound Hin)).
      - intros p st Hp He'. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]]; [discriminate He'|].
        intros E. cbn [lower_bound] in E. change (class_eqb nothing nothing = false) in E. rewrite class_eqb_refl in E. discriminate E. }
    (* the states the fold ends with *)
    assert (Hstep0: forall P A, In (P, A) (combine Ps As) -> forall s s', gw3 s ->
        unify env nf P A (Ongoing s) = Some (Ongoing s') ->
        gw3 s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP [HoP _]]. destruct (HAs A HA) as [HfA [HbA HqA]].
      destruct (mixed_parameter env wf declared declared_wf terminates finite not_expansive caller Qa
          (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) [] plain_nil (bf_nil env declared)
          gw3 gw3_capturable nf (fun k _ => rleaf_all k [])
          P A s s' HfP HoP (conj HfA (conj HbA (conj (owners_free_nil env A) HqA))) Hs E)
          as [Hs' [Hn' _]].
      split; [exact Hs'|exact Hn']. }
    destruct (mfold_chain env declared (gw3) nf _ u U Hstep0 Hwfu Hfold) as [[HgU HcU] _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep [Hkeep2 _]].
    assert (Hndo: NoDup (map fst ovars)).
    { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
      inversion H. apply IH. assumption. }
    (* the final values *)
    assert (Hfin: forall p S, In (p, S) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ static_upper_bound st = S /\ gfinal_of env U p = Constraints.final_value env st
        /\ of_fragment env declared (gfinal_of env U p) /\ caller (gfinal_of env U p) /\ gfits env declared st ref (gfinal_of env U p)).
    { intros p S Hin. destruct (Hkeep2 p _ (Hownu p S Hin) eq_refl eq_refl) as [st [Hl' [He' [_ Hs]]]].
      destruct (gfinal_value_fits env wf declared declared_wf terminates finite not_expansive caller U p st ref HgU Hl' He') as [Hf Hfit].
      assert (Ef: gfinal_of env U p = Constraints.final_value env st) by (unfold gfinal_of; rewrite Hl'; reflexivity).
      destruct (HgU p st Hl') as [_ [_ [Hw _]]]. destruct (Hw He') as [_ [_ [_ [_ [Hqu [Hql _]]]]]].
      exists st. split; [exact Hl'|]. split; [exact He'|]. split; [exact Hs|]. split; [exact Ef|]. rewrite Ef.
      split; [exact Hf|]. split; [|exact Hfit].
      unfold Constraints.final_value. destruct (is_non_nullable_nothing env (lower_bound st)); assumption. }
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
    (* the type arguments of the object, as those of c: class types without type parameters *)
    assert (Hzs': forall z, In z zs -> argument_in_fragment env z = true /\ nothing_is_bottom z = true /\ closed z = true).
    { destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
      assert (Hxs': forall x, In x xs -> argument_in_fragment env x = true /\ nothing_is_bottom x = true /\ closed x = true).
      { intros x Hx. split; [exact (Hxs x Hx)|].
        split; [exact (proj2 (nothing_is_bottom_root mo e xs Hno) x Hx)|exact (closed_parts mo e xs Hcl x Hx)]. }
      subst zs. destruct (Class_eq_dec e c) as [<-|Hne]; [rewrite class_eqb_refl; exact Hxs'|]. rewrite (class_eqb_false _ _ Hne).
      assert (Hta: forall y, In y xs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Hxs, Hy).
      destruct (supertype_arguments_to_generic env wf e c xs Hne He Hbe Hlx Hta) as [_ [_ [Hnb Hcb']]].
      destruct (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs) as [_ Hf].
      intros z Hz. split; [exact (Hf z Hz)|].
      split; [exact (Hnb (fun y Hy => proj1 (proj2 (Hxs' y Hy))) z Hz)|exact (Hcb' (fun y Hy => proj2 (proj2 (Hxs' y Hy))) z Hz)]. }
    (* the bindings: the type arguments of the object as c, and the final values of the function's *)
    assert (HlbC: forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z -> lookup_binding b p = Some z).
    { intros i p S z Hi Hz. assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
      rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz). reflexivity. }
    assert (HlbO: forall p S, In (p, S) ovars -> lookup_binding b p = Some (TypeArgument Model.invariant ref (gfinal_of env U p))).
    { intros p S Hin.
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
      exact (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (gfinal_of env U (fst v))) p S Hndo Hin). }
    assert (Hlb_in: forall q a, lookup_binding b q = Some a ->
        (exists i S z, nth_error cvars i = Some (q, S) /\ nth_error zs i = Some z /\ a = z)
        \/ exists S, In (q, S) ovars /\ a = TypeArgument Model.invariant ref (gfinal_of env U q)).
    { intros p a Hpb. rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a'|] eqn:Ec.
      - injection Hpb as <-. left. destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi Hz]].
        change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 S]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists i, S, a'. split; [exact Ev|]. split; [exact Hz|reflexivity].
      - right. destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (gfinal_of env U q)) p _ Hpb) as [Ea Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 S] [Hfst Hin]]. simpl in Hfst. subst p1. exists S. split; [exact Hin|exact Ea]. }
    assert (Hzarg: forall z, In z zs -> exists o x, z = TypeArgument Model.invariant o x /\ is_exact_ownership o = true
        /\ in_fragment env x = true /\ nothing_is_bottom x = true /\ closed x = true).
    { intros z Hz. pose proof (Hzx _ Hz) as Hex. destruct (Hzs' z Hz) as [_ [Hnz Hcz]].
      destruct z as [| | | |[] o x| |]; try discriminate Hex. simpl in Hex. apply andb_true_iff in Hex.
      cbn [nothing_is_bottom] in Hnz. destruct (closed_argument _ _ _ Hcz) as [_ Hcx].
      exists o, x. split; [reflexivity|]. split; [exact (proj1 Hex)|]. split; [exact (proj2 Hex)|]. split; [exact Hnz|exact Hcx]. }
    assert (Hpb: plain_values b).
    { intros q a Eq. destruct (Hlb_in q a Eq) as [[i [S [z [Hi [Hz ->]]]]]|[S [Hin ->]]].
      - destruct (Hzarg z (nth_error_In _ _ Hz)) as [o [x [-> [Ho [Hx _]]]]]. split; [destruct o; first [reflexivity|discriminate Ho]|].
        exists o, x. split; [reflexivity|exact (gfrag_not_nested env _ (in_fragment_is_gfrag env _ Hx))].
      - split; [reflexivity|]. destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf _]]]]]].
        exists ref, (gfinal_of env U q). split; [reflexivity|exact (gfrag_not_nested env _ (proj1 Hf))]. }
    assert (Hbv: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x).
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - destruct (Hzarg z (nth_error_In _ _ Hz)) as [o' [x' [Ez' [_ [Hx [Hnx Hcx]]]]]]. rewrite Ez' in Ez. injection Ez as _ Ex. rewrite Ex.
        split; [exact (of_fragment_of_class env declared _ Hx)|exact (classes_caller env declared ps (depth x') x' (le_n _) Hx Hnx Hcx)].
      - injection Ea as _ Ex. rewrite Ex. destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf [Hq _]]]]]]]. split; [exact Hf|exact Hq]. }
    assert (Hdomb: forall q, In q (map fst vars) -> bound_b b q = true).
    { intros q Hq'. unfold bound_b. unfold vars in Hq'. rewrite map_app in Hq'. apply in_app_or in Hq'.
      destruct Hq' as [Hq'|Hq']; apply in_map_iff in Hq'; destruct Hq' as [[q1 S] [Hfst Hin]]; simpl in Hfst; subst q1.
      - destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars zs i _ ltac:(rewrite length_map in Hlz; lia) Hi)
            as [z Hz].
        rewrite (HlbC i q S z Hi Hz). reflexivity.
      - rewrite (HlbO q S Hin). reflexivity. }
    assert (Hbound: forall t, vars_in (fun q => existsb (param_eqb q) (map fst vars)) t = true -> vars_in (bound_b b) t = true).
    { apply vars_in_mono. intros q E. apply existsb_exists in E. destruct E as [q' [Hq' Eq]]. apply param_eqb_eq in Eq. subst q'.
      exact (Hdomb q Hq'). }
    (* none of the type parameters of the caller is bound in b, nor so their ownerships *)
    assert (Hnone: forall q, In q ps -> lookup_binding b q = None).
    { intros q Hq. pose proof (Hdis q Hq) as Hn. unfold vars in Hn. rewrite map_app in Hn. rewrite Hbdef, lookup_app.
      assert (Hnc: ~ In q (parameter_ids env c)) by (rewrite <- Hids; intros H; apply Hn; apply in_or_app; left; exact H).
      rewrite (lookup_combine_none _ zs q Hnc: lookup_binding (bindings_of env c zs) q = None).
      apply lookup_map_none. intros H. apply Hn. apply in_or_app. right. exact H. }
    assert (Hown': forall t, caller t -> owners_free env b t)
        by (intros t Ht; exact (mentions_only_free env wf ps b Hnone t (proj2 (proj2 Ht)))).
    assert (Hdu: dom b u).
    { intros q o z Eq. destruct (Hlb_in q _ Eq) as [[i [S [z' [Hi [Hz _]]]]]|[S [Hin _]]].
      - destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy]. eexists. exact (Hcap i q S y Hi Hy).
      - eexists. exact (Hownu q S Hin). }
    assert (HdU: dom b U) by exact (dom_forward2 b u U (proj1 Hwfu) (fold_keeps_exact_unify env nf _ u U Hfold) Hdu).
    (* what the type variables stand for at run time *)
    assert (Hrsat: rsat2 b U).
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - (* a type parameter of c: the type argument of the object, within that of the receiver, instantiated *)
        destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        exists (mkVariableState S y y true true). split; [exact (Hkeep q _ (Hcap i q S y Hi Hy) eq_refl)|].
        destruct (Hzarg z (nth_error_In _ _ Hz)) as [o' [x' [Ez' [_ [Hx [_ Hcx]]]]]]. rewrite Ez' in Ez. injection Ez as Eo Ex. subst o' x'.
        rewrite (instantiate_class_types (depth x) x (le_n _) Hx Hcx).
        destruct (Hys y (nth_error_In _ _ Hy)) as [Hgy [Hry [[HcX Hmy] _]]].
        destruct y as [| | | |vb ob X| |]; try discriminate Hgy.
        unfold rfits. cbn [is_exact upper_bound lower_bound].
        pose proof (Forall2_nth_error _ zs (map (instantiate env sigma) ys') i _ _ Hpw Hz (map_nth_error _ i _ Hy)) as Ezy.
        rewrite Ez' in Ezy. destruct f1 as [|K1]; [discriminate Ezy|].
        exists vb, ob, X, K1. split; [reflexivity|]. split; [reflexivity|]. split; [split; [exact Hgy|exact Hry]|].
        split; [exact HcX|]. split; [exact (proj1 Hmy)|exact Ezy].
      - (* a type parameter of the function: its final value, instantiated *)
        injection Ea as Eo Ex. subst o x.
        destruct (Hfin q S Hin) as [st [HlU [He2 [_ [_ [Hff [Hqf Hfit]]]]]]].
        exists st. split; [exact HlU|]. unfold rfits. rewrite He2. exists (gfinal_of env U q).
        split; [exact Hff|]. split; [exact Hqf|]. split; [exact Hfit|reflexivity]. }
    split.
    - (* the final values, within the static upper bounds at run time *)
      intros p S Hin C HC. destruct (Hfin p S Hin) as [st [HlU [He' [Hs [Ef [Hf [Hq Hfit]]]]]]].
      destruct (Hst p S Hin) as [_ [Hsv [Hcl' _]]].
      destruct (HgU p st HlU) as [_ [_ [Hw _]]]. destruct (Hw He') as [_ [_ [_ [Hfl [_ [Hql [_ Hok]]]]]]].
      unfold gstatic_ok in Hok. rewrite Hs in Hok. destruct (no_vars S) eqn:Ens.
      + (* without type variables: below the upper bound, which is below it, and its components *)
        destruct (Hcl' eq_refl) as [HfS HqS]. unfold gfits in Hfit. rewrite He' in Hfit. destruct Hfit as [_ Hup].
        destruct (bound_component_of env wf declared declared_wf terminates finite not_expansive caller (caller_component env declared ps)
            (caller_nullable_component env declared ps)
            S C HfS HqS HC) as [HfC [HqC HSC]].
        unfold rinst. rewrite (free_unmentioned env b Hpb C (proj1 HfC) (unmentioned env b C (proj1 HfC) (Hown' C HqC))).
        exact (subst_below _ C Hq HqC (below_trans env wf declared declared_wf terminates finite not_expansive _ S C Hf HfS HfC
            (Hok _ Hf Hup) HSC)).
      + (* with them: the lower bound, checked against it at run time *)
        destruct Hok as [[Hcomp _] _]. destruct (Hcomp C HC) as [HCi [HCo _]].
        pose proof (Hlow p S st Hin Ens HlU) as Hnn.
        assert (Exl: gfinal_of env U p = lower_bound st) by (rewrite Ef; unfold Constraints.final_value; rewrite Hnn; reflexivity).
        assert (Hvb: vars_in (fun q => param_eqb q p || bound_b b q) S = true).
        { apply (vars_in_mono (bound_b b)); [intros q E; rewrite E; apply orb_true_r|].
          apply Hbound. apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ Hsv). }
        pose proof (HcU p st HlU He' Hnn) as Hchk. unfold rstatic_checked in Hchk. rewrite Hs in Hchk.
        pose proof (Hchk Ens b Hpb Hbv HdU (Hown' _ Hql) Hvb Hrsat C HC) as [f Hc'].
        exists f. rewrite Exl. unfold rinst in Hc' |- *.
        rewrite (free_candidate env b p (lower_bound st) C Hpb (proj1 Hfl) (unmentioned env b _ (proj1 Hfl) (Hown' _ Hql))
            (ifrag_plain_variables env wf C HCi HCo)) in Hc'.
        rewrite (free_ext env _ b (with_value_same b p (lower_bound st) ltac:(rewrite (HlbO p S Hin), Exl; reflexivity)) C) in Hc'.
        exact Hc'.
    - (* each argument, in turn *)
      intros P A HPA.
      destruct (rfold2 b (fun x inner => let '(P', A') := x in unify env nf P' A' inner)
          (fun x => let '(P', A') := x in exists f,
              unify env f (instantiate env sigma (pinstance env (instantiate_free env b) P')) (instantiate env sigma A') (Ongoing []) = Some (Ongoing []))
          (combine Ps As) u U) as [_ [_ [_ [_ Hall]]]].
      + intros [P' A']. apply unify_keeps_failure.
      + intros [P' A'] Hin s1 s1' Hs1 Hd1 E. apply in_combine_l in Hin as HP'. apply in_combine_r in Hin as HA'.
        destruct (HPs P' HP') as [HfP [HoP HvP]]. destruct (HAs A' HA') as [HfA [HbA HqA]].
        destruct (mixed_parameter env wf declared declared_wf terminates finite not_expansive caller Qa
            (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_root env declared ps)
            (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
            (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) [] plain_nil (bf_nil env declared)
            gw (gwf2_capturable env declared caller) nf (fun k _ => gleaf k [])
            P' A' s1 s1' HfP HoP (conj HfA (conj HbA (conj (owners_free_nil env A') HqA)))
            Hs1 E) as [Hs1' [Hm1 _]].
        split; [exact Hs1'|]. split; [exact Hm1|]. split; [exact (unify_keeps_exact env nf P' A' s1 s1' E)|].
        intros Hr. pose proof (Hbound P' HvP) as HvP'.
        exact (runtime_mparameter b Hpb Hbv nf P' A' s1 s1' HfP (HPg P' HP') HoP HvP' (conj HfA (conj HbA (conj (Hown' A' HqA) HqA)))
            Hs1 Hd1 E Hr).
      + exact (proj1 Hwfu).
      + exact Hdu.
      + exact Hfold.
      + destruct (Hall Hrsat (P, A) HPA) as [f Ef]. exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.

End Bounded.

End Receivers.

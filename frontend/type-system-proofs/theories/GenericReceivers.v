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
From Stdlib Require Import Bool List Arith Lia Sorting.
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
Hypothesis tame: tame_inheritance env.
Hypothesis intersect_in_fragment: intersect_always_stays_in_fragment env declared.
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
Let caller_ref_apply' := fun gm nn x (_: of_fragment env declared x) (Hx: caller x) => caller_ref_apply env wf declared ps gm nn x Hx.
Let caller_rewrap' := caller_rewrap env declared ps.

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
    destruct (substitution_wide env declared sigma (max K1 K2) n y x wf declared_wf terminates finite tame Hsf
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
    exact (ground_trans env wf declared declared_wf terminates finite tame f1 f2 X Y Z HX HY HZ H1 H2).
Qed.

Lemma ground_takes_bottom: forall m y, ground env y = true -> exists f, unify env f y (RootResolved m nothing []) (Ongoing []) = Some (Ongoing []).
Proof.
    intros m y Hy. exact (below_nothing env wf declared declared_wf terminates finite tame m y (ground_of_fragment env declared y Hy)).
Qed.

Lemma ground_below_top: forall y, ground env y = true -> exists f, unify env f top_type y (Ongoing []) = Some (Ongoing []).
Proof.
    intros y Hy. exact (below_top env wf declared declared_wf terminates finite tame y (ground_of_fragment env declared y Hy)).
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
    destruct (gtarget_leaf env wf declared declared_wf terminates finite tame supertype_in_fragment supertype_above
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
      destruct (below_refl env wf declared declared_wf terminates finite tame X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K (proj2 Hc))).
      + destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; exact EX))) as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K Hc)).
      + destruct (below_bottom env wf declared declared_wf terminates finite tame X HfX) as [kb Eb].
        destruct (subst_below A bottom_type HcA caller_bottom'
            (Hgf bottom_type (bottom_of_fragment env wf declared) ltac:(exists kb; cbn [compare_variances]; exact Eb))) as [f1 E1].
        exact (rtrans _ _ _ HgA ground_bottom Hz (ex_intro _ f1 E1) (ground_takes_bottom _ z Hz)).
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
    destruct (gassignee_leaf env wf declared declared_wf terminates finite tame intersect_in_fragment intersect_below
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
      destruct (below_refl env wf declared declared_wf terminates finite tame X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below X A HcX HcA (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ Hz HgX HgA (ex_intro _ K (proj1 Hc)) (ex_intro _ f1 E1)).
      + destruct (below_top env wf declared declared_wf terminates finite tame X HfX) as [kt Et].
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
    - change (without_null env an = an). exact (without_null_unchanged env an (non_null_not_nullable env an Hn)).
    - exact (without_null_not_nullable_intersection env cs (gfrag_intersection_not_nullable env cs Hx)).
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

(* A ground type made nullable is ground *)
Lemma ground_rewrap_ground: forall X, ground env X = true -> ground env (rewrap_nullable X) = true.
Proof.
    intros X HX. destruct (ground_cases env X HX) as [[m [c [args ->]]]|[[m [c [args ->]]]|[[ys [-> _]]|[ys [-> _]]]]]; try exact HX.
    cbn [rewrap_nullable]. unfold ground in HX |- *. apply andb_true_iff in HX. destruct HX as [Hg Hr].
    apply andb_true_iff. split; [|exact Hr].
    change (non_null env (Intersection ys) && gfrag env (Intersection ys) = true). rewrite Hg, andb_true_r.
    change (negb (is_nullable env (Intersection ys)) = true). apply negb_true_iff. exact (gfrag_intersection_not_nullable env ys Hg).
Qed.

(* What a ground type is assigned, it is assigned without null *)
Lemma ground_assignee_without_null: forall f T y, ground env T = true -> ground env y = true ->
    unify env f T y (Ongoing []) = Some (Ongoing []) -> unify env f T (without_null env y) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f T y HT Hy H. destruct (is_nullable env T) eqn:En.
    - destruct f as [|f]; [discriminate H|].
      destruct (ground_cases env T HT) as [[mt [ct [targs ->]]]|[[mt [ct [targs ->]]]|[[ts [-> _]]|[ts [-> _]]]]];
          try discriminate En; try (rewrite (ground_intersection_not_nullable env ts (or_introl HT)) in En; discriminate En);
          rewrite (ground_nullable_target env f _ _ _ Hy) in H;
          rewrite (ground_nullable_target env f _ _ _ (ground_without_null env y Hy)), (ground_without_null_idempotent env y Hy); exact H.
    - rewrite (ground_non_null_without_null env y Hy (ground_non_null env f T y [] [] HT Hy En H)). exact H.
Qed.

Lemma shape_of_fragment: forall A, gfrag env A = true -> match A with Error _ _ | TypeVariable _ => False | _ => True end.
Proof.
    intros A HA. destruct (gfrag_cases env A HA) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* A mutability given to a type variable, at run time                                              *)
(* ---------------------------------------------------------------------------------------------- *)

(* A ground type, of a mutability given to it, or narrowed: ground *)
Lemma ground_with_mutability_any: forall k z, ground env z = true -> ground env (with_mutability env k z) = true.
Proof.
    intros k z Hz. unfold ground in Hz |- *. apply andb_true_iff in Hz. destruct Hz as [Hg Hn]. apply andb_true_iff. split.
    - exact (gfrag_with_mutability env wf declared declared_wf k z Hg).
    - clear Hg. revert z k Hn. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] k Hn; cbn [no_refs] in Hn; try discriminate Hn.
      + exact Hn.
      + cbn [with_mutability]. pose proof (IH n k Hn) as H'. destruct (with_mutability env k n); exact H'.
      + exact (IH n k Hn).
      + cbn [with_mutability no_refs].
        generalize (fold_left intersect_mutability (map (fun c0 => assignment_mutability env (with_mutability env k c0)) cs) readonly) as C.
        intros C. induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb map] in Hn |- *. apply andb_true_iff in Hn.
        rewrite (IH c C (proj1 Hn)), (IHc (proj2 Hn)). reflexivity.
Qed.

Lemma no_refs_without_null: forall t, no_refs t = true -> no_refs (without_null env t) = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; cbn [without_null no_refs] in H |- *; try exact H;
        try exact (IH n H).
    destruct (forallb (is_nullable env) cs); [|exact H]. cbn [no_refs].
    induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
    rewrite (IH c (proj1 H)). exact (IHc (proj2 H)).
Qed.

Lemma no_refs_with_mutability: forall k t, no_refs t = true -> no_refs (with_mutability env k t) = true.
Proof.
    fix IH 2. intros k [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] H; cbn [with_mutability no_refs] in H |- *; try exact H.
    - pose proof (IH k n H) as Hn. destruct (with_mutability env k n); exact Hn.
    - exact (IH k n H).
    - match goal with |- context [map (with_mutability env ?x) _] => generalize x end. intros k'.
      induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb] in H |- *. apply andb_true_iff in H.
      rewrite (IH k' c (proj1 H)). exact (IHc (proj2 H)).
Qed.

(* An intersection of ground types, as ofComponents makes it, of the fragment, is ground *)
Lemma ground_of_components: forall ys, (forall y, In y ys -> ground env y = true) ->
    gfrag env (of_components env (flat_map intersected_components ys)) = true ->
    ground env (of_components env (flat_map intersected_components ys)) = true.
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

Lemma ground_ref_apply: forall gm nn z, ground env z = true -> ground env (ref_apply env gm nn z) = true.
Proof.
    intros gm nn z Hz. unfold ref_apply. cbn zeta.
    destruct gm as [m|]; destruct nn; first [apply ground_without_null|idtac]; first [exact (ground_with_mutability_any _ z Hz)|exact Hz].
Qed.

(* At run time, a type of generic code is assigned as no more than in generic code: it is below `m Any`
   without null *)
Lemma runtime_mutability: forall A m, of_fragment env declared A -> caller A ->
    Model.is_subtype_of (assignment_mutability env A) m = true ->
    Model.is_subtype_of (assignment_mutability env (instantiate env sigma A)) m = true.
Proof.
    intros A m HA HcA Hm.
    destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 HA)) as [HgN [HnN _]].
    assert (HfN: of_fragment env declared (nullable_assignee env A)) by (split; [exact HgN|exact I]).
    pose proof (caller_nullable_assignee A (proj1 HA) HcA) as HcN.
    assert (EN: assignment_mutability env (nullable_assignee env A) = assignment_mutability env A)
        by (rewrite <- (without_null_nullable_assignee A (proj1 HA)); apply (without_null_keeps_assignment_mutability env ranked)).
    pose proof (below_any_of env wf declared declared_wf terminates finite tame m _ HfN HnN ltac:(rewrite EN; exact Hm)) as Hb.
    destruct (subst_below _ _ HcN (caller_any env wf declared ps m) Hb) as [f Hf].
    destruct (instance_ground _ HcN) as [_ [_ HgI]]. destruct (instance_ground _ (caller_any env wf declared ps m)) as [_ [_ Hga]].
    pose proof (ground_mutability env wf f _ _ [] [] Hga HgI Hf) as Hm'.
    rewrite instantiate_class in Hm'. cbn [map assignment_mutability] in Hm'. rewrite (wf_any_is_not_const env wf) in Hm'.
    rewrite <- (without_null_keeps_assignment_mutability env ranked (instantiate env sigma A)), <- (instance_nullable_assignee A (proj1 HA) HcA),
        (without_null_keeps_assignment_mutability env ranked). exact Hm'.
Qed.


(* The meet of mutabilities *)
Lemma intersect_below_eq: forall a b, Model.is_subtype_of a b = true -> intersect_mutability a b = a.
Proof. intros [] [] H; first [reflexivity|discriminate H]. Qed.

Lemma intersect_readonly: forall a, intersect_mutability readonly a = a.
Proof. intros []; reflexivity. Qed.

Lemma intersect_monotone: forall a a' b b', Model.is_subtype_of a a' = true -> Model.is_subtype_of b b' = true ->
    Model.is_subtype_of (intersect_mutability a b) (intersect_mutability a' b') = true.
Proof. intros [] [] [] [] H1 H2; first [reflexivity|discriminate H1|discriminate H2]. Qed.

Lemma fold_meet_with: forall (f: EType -> Mutability) j l a,
    fold_left intersect_mutability (map (fun x => intersect_mutability (f x) j) l) (intersect_mutability a j)
    = intersect_mutability (fold_left intersect_mutability (map f l) a) j.
Proof.
    intros f j l. induction l as [|x l IH]; intros a; [reflexivity|]. cbn [map fold_left].
    replace (intersect_mutability (intersect_mutability a j) (intersect_mutability (f x) j))
        with (intersect_mutability (intersect_mutability a (f x)) j) by (destruct a, j, (f x); reflexivity).
    exact (IH _).
Qed.

Lemma fold_meet_cons: forall (f: EType -> Mutability) j l, l <> [] ->
    fold_left intersect_mutability (map (fun x => intersect_mutability (f x) j) l) readonly
    = intersect_mutability (fold_left intersect_mutability (map f l) readonly) j.
Proof.
    intros f j [|x l] Hne; [contradiction|]. cbn [map fold_left]. rewrite !intersect_readonly. exact (fold_meet_with f j l (f x)).
Qed.

Lemma fold_meet_const: forall (A: Type) (l: list A) j, l <> [] -> fold_left intersect_mutability (map (fun _ => j) l) readonly = j.
Proof.
    intros A [|x l] j Hne; [contradiction|]. clear Hne. cbn [map fold_left]. rewrite intersect_readonly. clear x. revert j.
    induction l as [|y l IH]; intros j; [reflexivity|]. cbn [map fold_left].
    replace (intersect_mutability j j) with j by (destruct j; reflexivity). exact (IH j).
Qed.

Lemma fold_meet_monotone: forall (f g: EType -> Mutability) l a a', Model.is_subtype_of a a' = true ->
    (forall x, In x l -> Model.is_subtype_of (f x) (g x) = true) ->
    Model.is_subtype_of (fold_left intersect_mutability (map f l) a) (fold_left intersect_mutability (map g l) a') = true.
Proof.
    intros f g l. induction l as [|x l IH]; intros a a' Ha H; [exact Ha|]. cbn [map fold_left].
    apply IH; [apply intersect_monotone; [exact Ha|exact (H x (or_introl eq_refl))]|intros y Hy; exact (H y (or_intror Hy))].
Qed.

Lemma fold_meet_exclusive: forall l a, In exclusive l -> fold_left intersect_mutability l a = exclusive.
Proof. intros l a H. apply mutability_subtype_of_exclusive. exact (fold_intersect_below_element l a exclusive H). Qed.

(* The type a type parameter of the caller is bound to is assigned as no more than its bound *)
Lemma binding_below_bound: forall q o y, In q ps -> lookup_binding sigma q = Some (TypeArgument Model.invariant o y) ->
    Model.is_subtype_of (assignment_mutability env y) (assignment_mutability env (parameter_bound env q)) = true.
Proof.
    intros q o y Hq Ey. destruct (Hwithin q Hq) as [o' [y' [Ey' [_ [f Hf]]]]]. rewrite Ey in Ey'. injection Ey' as <- <-.
    destruct (Hdeclared q Hq) as [Ht [Hb Hm]].
    assert (Hc: caller (declared q)) by (split; [exact (tfrag_wtfrag env wf _ Ht)|split; [exact Hb|exact Hm]]).
    destruct (instance_ground _ Hc) as [K [HbD HgD]].
    rewrite (inst_nested_instantiate env wf sigma K [] (declared q) Ht HbD) in Hf.
    pose proof (in_fragment_ground env y (Hsf q o y Ey)) as Gy.
    pose proof (ground_mutability env wf f _ _ [] [] HgD Gy Hf) as H1.
    rewrite <- (bw_declared env declared declared_wf q).
    apply (mutability_subtype_trans _ _ _ H1). apply (runtime_mutability _ _ (conj (bw_gfrag env declared declared_wf q) I) Hc).
    apply mutability_is_subtype_of_refl.
Qed.

(* A class type, nullable or not, of a mutability given to it: of that mutability, but where it is const *)
Lemma frag_with_mutability: forall j y, in_fragment env y = true ->
    mutability_of env (with_mutability env j y) = (if top_const env y then immutable else j)
    /\ assignment_mutability env (with_mutability env j y) = (if top_const env y then exclusive else j)
    /\ (top_const env y = true -> forall j', with_mutability env j y = with_mutability env j' y)
    /\ (top_const env y = false -> mutability_of env y = assignment_mutability env y).
Proof.
    intros j y Hy. destruct (fragment_cases env y Hy) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        cbn [with_mutability rewrap_nullable mutability_of assignment_mutability top_const];
        destruct (is_const (declaration_of env c));
        (split; [reflexivity|split; [reflexivity|split; [intros E j'; first [reflexivity|discriminate E]|intros E; first [reflexivity|discriminate E]]]]).
Qed.

(* Instantiated, a reference to a type parameter of the caller given a mutability, no more than its
   own, is what the type parameter is bound to given the mutability, as instantiating it gives it:
   the type it is bound to is within its bound *)
Lemma instance_given_generic: forall gm nn q m, caller (Generic (mkGenericRef gm nn q [])) ->
    instantiate env sigma (with_mutability env (intersect_mutability (mutability_of env (Generic (mkGenericRef gm nn q []))) m)
        (Generic (mkGenericRef gm nn q [])))
    = with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma (Generic (mkGenericRef gm nn q [])))) m)
        (instantiate env sigma (Generic (mkGenericRef gm nn q []))).
Proof.
    intros gm nn q m Hc. destruct Hc as [_ [_ [Hq _]]].
    destruct (Hwithin q Hq) as [o [y [Ey [Ho _]]]]. pose proof (Hsf q o y Ey) as Hy. pose proof (in_fragment_is_gfrag env y Hy) as Gy.
    pose proof (binding_below_bound q o y Hq Ey) as Hyb.
    set (D := parameter_bound env q) in Hyb.
    rewrite (mutability_of_generic env ranked), (effective_bound_eq env ranked).
    cbn [with_type_variables variables_of given_mutability is_narrowed param_of with_mutability].
    rewrite (proj1 (instantiate_exact_generic env sigma (mkGenericRef gm nn q []) o y Ey Ho Gy)).
    rewrite (proj1 (instantiate_exact_generic env sigma (mkGenericRef (Some _) nn q []) o y Ey Ho Gy)).
    fold D. unfold inst_ref, inst_fit. cbn [is_narrowed given_mutability].
    (* without null where narrowed, as the mutability is *)
    assert (Hcore: forall k, intersect_mutability (mutability_of env y) k
            = intersect_mutability (mutability_of env (match gm with Some m' => with_mutability env (intersect_mutability (mutability_of env y) m') y | None => y end)) m
        \/ top_const env y = true ->
        with_mutability env (intersect_mutability (mutability_of env y) k) y
        = with_mutability env (intersect_mutability (mutability_of env (match gm with Some m' => with_mutability env (intersect_mutability (mutability_of env y) m') y | None => y end)) m)
            (match gm with Some m' => with_mutability env (intersect_mutability (mutability_of env y) m') y | None => y end)).
    { intros k [E|Et].
      - rewrite E. destruct gm; [rewrite with_mutability_twice|]; reflexivity.
      - destruct gm; [rewrite with_mutability_twice|]; exact (proj1 (proj2 (proj2 (frag_with_mutability _ y Hy))) Et _). }
    assert (Hk: intersect_mutability (mutability_of env y)
            (intersect_mutability (mutability_of env (match gm with Some m' => with_mutability env m' D | None => D end)) m)
        = intersect_mutability (mutability_of env (match gm with Some m' => with_mutability env (intersect_mutability (mutability_of env y) m') y | None => y end)) m
        \/ top_const env y = true).
    { destruct (top_const env y) eqn:Ety; [right; reflexivity|left].
      pose proof (proj2 (proj2 (proj2 (frag_with_mutability readonly y Hy))) Ety) as Emy. rewrite <- Emy in Hyb.
      destruct gm as [m'|].
      - rewrite (proj1 (frag_with_mutability _ y Hy)), Ety.
        destruct (top_const env D) eqn:EtD.
        + rewrite (top_const_assigned_exclusive env ranked D EtD) in Hyb. rewrite (mutability_subtype_of_exclusive _ Hyb).
          destruct (mutability_of env (with_mutability env m' D)), m', m; reflexivity.
        + assert (EmD: mutability_of env (with_mutability env m' D) = m').
          { rewrite <- (not_top_const env wf (with_mutability env m' D) ltac:(rewrite (top_const_with_mutability env wf); exact EtD)).
            rewrite (assignment_with_mutability env wf declared declared_wf m' D (parameter_bound_gfrag env declared declared_wf q)), EtD.
            reflexivity. }
          rewrite EmD, intersect_mutability_assoc. reflexivity.
      - pose proof (mutability_subtype_trans _ _ _ Hyb (assignment_mutability_below env ranked D)) as HyD.
        rewrite <- intersect_mutability_assoc, (intersect_below_eq _ _ HyD). reflexivity. }
    destruct nn.
    - rewrite !(mutability_without_null env wf), (with_mutability_without_null env wf). f_equal. exact (Hcore _ Hk).
    - exact (Hcore _ Hk).
Qed.


(* A class type of a mutability given to it: of that mutability, but where it is const *)
Lemma class_with_mutability: forall j y, is_class y = true ->
    assignment_mutability env (with_mutability env j y) = (if top_const env y then exclusive else j)
    /\ mutability_of env (with_mutability env j y) = (if top_const env y then immutable else j)
    /\ top_const env (with_mutability env j y) = top_const env y
    /\ (top_const env y = false -> mutability_of env y = assignment_mutability env y).
Proof.
    intros j [m c args| | | | | |] H; try discriminate H. cbn [with_mutability assignment_mutability mutability_of top_const].
    destruct (is_const (declaration_of env c)); (split; [reflexivity|split; [reflexivity|split; [reflexivity|intros E; first [reflexivity|discriminate E]]]]).
Qed.

(* The instance of a reference to a type parameter of the caller: no more mutable than the reference,
   but where it is const; exclusive or const where the bound is const *)
Lemma generic_instance_mutability: forall gm nn q, caller (Generic (mkGenericRef gm nn q [])) ->
    (top_const env (instantiate env sigma (Generic (mkGenericRef gm nn q []))) = false ->
        Model.is_subtype_of (mutability_of env (instantiate env sigma (Generic (mkGenericRef gm nn q []))))
            (mutability_of env (Generic (mkGenericRef gm nn q []))) = true)
    /\ (top_const env (Generic (mkGenericRef gm nn q [])) = true ->
        top_const env (instantiate env sigma (Generic (mkGenericRef gm nn q []))) = true
        \/ mutability_of env (instantiate env sigma (Generic (mkGenericRef gm nn q []))) = exclusive).
Proof.
    intros gm nn q Hc. destruct Hc as [_ [_ [Hq _]]].
    destruct (Hwithin q Hq) as [o [y [Ey [Ho _]]]]. pose proof (Hsf q o y Ey) as Hy. pose proof (in_fragment_is_gfrag env y Hy) as Gy.
    pose proof (binding_below_bound q o y Hq Ey) as Hyb.
    set (D := parameter_bound env q) in Hyb.
    rewrite (proj1 (instantiate_exact_generic env sigma (mkGenericRef gm nn q []) o y Ey Ho Gy)).
    rewrite (mutability_of_generic env ranked), (top_const_generic env ranked), (effective_bound_eq env ranked).
    cbn [with_type_variables variables_of given_mutability is_narrowed param_of]. fold D.
    unfold inst_ref, inst_fit. cbn [is_narrowed given_mutability].
    assert (Hn: forall z, mutability_of env (if nn then without_null env z else z) = mutability_of env z
        /\ top_const env (if nn then without_null env z else z) = top_const env z)
        by (intros z; destruct nn; [exact (conj (mutability_without_null env wf z) (top_const_without_null env ranked z))|split; reflexivity]).
    rewrite !(proj1 (Hn _)), !(proj2 (Hn _)).
    assert (EtD: top_const env (match gm with Some m' => with_mutability env m' D | None => D end) = top_const env D)
        by (destruct gm; [exact (top_const_with_mutability env wf _ D)|reflexivity]).
    assert (Ety: top_const env (match gm with Some m' => with_mutability env (intersect_mutability (mutability_of env y) m') y | None => y end)
        = top_const env y) by (destruct gm; [exact (top_const_with_mutability env wf _ y)|reflexivity]).
    rewrite EtD, Ety. split.
    - intros Hty. pose proof (proj2 (proj2 (proj2 (frag_with_mutability readonly y Hy))) Hty) as Emy. rewrite <- Emy in Hyb.
      destruct gm as [m'|].
      + rewrite (proj1 (frag_with_mutability _ y Hy)), Hty.
        destruct (top_const env D) eqn:EtD'.
        * rewrite (top_const_assigned_exclusive env ranked D EtD') in Hyb. rewrite (mutability_subtype_of_exclusive _ Hyb). reflexivity.
        * rewrite <- (not_top_const env wf (with_mutability env m' D) ltac:(rewrite (top_const_with_mutability env wf); exact EtD')).
          rewrite (assignment_with_mutability env wf declared declared_wf m' D (parameter_bound_gfrag env declared declared_wf q)), EtD'.
          apply intersect_mutability_right.
      + exact (mutability_subtype_trans _ _ _ Hyb (assignment_mutability_below env ranked D)).
    - intros EtD'. destruct (top_const env y) eqn:Hty; [left; reflexivity|right].
      pose proof (proj2 (proj2 (proj2 (frag_with_mutability readonly y Hy))) Hty) as Emy.
      rewrite (top_const_assigned_exclusive env ranked D EtD') in Hyb. rewrite <- Emy in Hyb.
      pose proof (mutability_subtype_of_exclusive _ Hyb) as Ex.
      destruct gm as [m'|]; [rewrite (proj1 (frag_with_mutability _ y Hy)), Hty, Ex; reflexivity|exact Ex].
Qed.

Lemma mutability_rewrap: forall y, mutability_of env (rewrap_nullable y) = mutability_of env y.
Proof. intros [| | | | | |]; reflexivity. Qed.

(* Instantiated, a type of generic code given a mutability, no more than its own, is its instance given
   the mutability, as instantiating it gives it *)
Lemma instance_given: forall m x, caller x ->
    instantiate env sigma (with_mutability env (intersect_mutability (mutability_of env x) m) x)
    = with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma x)) m) (instantiate env sigma x).
Proof.
    (* a class type or a reference, nullable or not *)
    assert (Hw: forall m x, caller x -> wfrag env x = true ->
        instantiate env sigma (with_mutability env (intersect_mutability (mutability_of env x) m) x)
        = with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma x)) m) (instantiate env sigma x)).
    { intros m x Hc Hwx.
      destruct (wfrag_cases env wf x Hwx) as [[m0 [c [args [-> _]]]]|[[m_bot ->]|[[m0 [c [args [-> _]]]]|[[[gm nn q vs] [-> Hg]]|[[gm nn q vs] [-> Hg]]]]]];
          try reflexivity; (destruct vs; [|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv]).
      - exact (instance_given_generic gm nn q m Hc).
      - pose proof (instance_given_generic gm nn q m (caller_nullable env declared ps _ Hc)) as E.
        pose proof (rewrap_sigma (Generic (mkGenericRef gm nn q []))) as ER. cbn [rewrap_nullable] in ER.
        change (with_mutability env (intersect_mutability (mutability_of env (Nullable (Generic (mkGenericRef gm nn q [])))) m)
            (Nullable (Generic (mkGenericRef gm nn q []))))
            with (rewrap_nullable (with_mutability env (intersect_mutability (mutability_of env (Generic (mkGenericRef gm nn q []))) m)
                (Generic (mkGenericRef gm nn q [])))).
        rewrite rewrap_sigma, E, ER, with_mutability_rewrap, mutability_rewrap. reflexivity. }
    (* an intersection: its components take the mutability they are assigned as in common *)
    assert (Hint: forall cs m, caller (Intersection cs) -> wcomponents env cs = true ->
        instantiate env sigma (with_mutability env (intersect_mutability (mutability_of env (Intersection cs)) m) (Intersection cs))
        = with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma (Intersection cs))) m)
            (instantiate env sigma (Intersection cs))).
    { intros cs m Hc Hcs. destruct (wcomponents_facts env cs Hcs) as [Hlen Hcomp].
      assert (Hne: cs <> []) by (intros ->; simpl in Hlen; lia).
      pose proof (fun c Hin => caller_component env declared ps cs c Hc Hin) as Hcc.
      set (k := intersect_mutability (mutability_of env (Intersection cs)) m).
      assert (HC: forall c, In c cs -> assignment_mutability env (with_mutability env k c) = if top_const env c then exclusive else k).
      { intros c Hin. destruct (Hcomp c Hin) as [Hsh Hwc].
        destruct (wfrag_cases env wf c Hwc) as [[m0 [cl [args [-> _]]]]|[[m_bot ->]|[[m0 [cl [args [-> _]]]]|[[g [-> Hg]]|[g [-> Hg]]]]]];
            try discriminate Hsh.
        - cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
        - unfold bottom_type. cbn [with_mutability assignment_mutability top_const]. destruct (is_const _); reflexivity.
        - exact (assignment_given env wf (S (tdepth env (Generic g))) (Generic g) k (le_n _) (sfrag_tfrag env _ Hwc)). }
      set (C := if existsb (top_const env) cs then exclusive else k).
      assert (EC: with_mutability env k (Intersection cs) = Intersection (map (with_mutability env C) cs))
          by (cbn [with_mutability]; unfold C; rewrite (common_given env k cs Hne HC); reflexivity).
      pose proof (common_below env k cs (intersect_mutability_left _ _)) as HCb. fold C in HCb.
      assert (Ecomp: forall c, In c cs -> instantiate env sigma (with_mutability env C c)
          = with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma c)) C) (instantiate env sigma c)).
      { intros c Hin. pose proof (Hw C c (Hcc c Hin) (proj2 (Hcomp c Hin))) as E.
        replace (intersect_mutability (mutability_of env c) C) with C in E
            by (rewrite intersect_mutability_comm; exact (eq_sym (intersect_below_eq _ _ (HCb c Hin)))).
        exact E. }
      (* the components, instantiated: no more mutable than in generic code, but where they are const *)
      assert (Hmc: forall c, In c cs -> (top_const env (instantiate env sigma c) = false ->
              Model.is_subtype_of (mutability_of env (instantiate env sigma c)) (mutability_of env c) = true)
          /\ (top_const env c = true -> top_const env (instantiate env sigma c) = true \/ mutability_of env (instantiate env sigma c) = exclusive)).
      { intros c Hin. destruct (Hcomp c Hin) as [Hsh Hwc].
        destruct (wfrag_cases env wf c Hwc) as [[m0 [cl [args [-> _]]]]|[[m_bot ->]|[[m0 [cl [args [-> _]]]]|[[[gm nn q vs] [-> Hg]]|[g [-> Hg]]]]]];
            try discriminate Hsh.
        - split; [intros _; apply mutability_is_subtype_of_refl|intros E; left; exact E].
        - split; [intros _; apply mutability_is_subtype_of_refl|intros E; left; exact E].
        - destruct vs; [|destruct Hg as [_ [_ [Hv _]]]; discriminate Hv]. exact (generic_instance_mutability gm nn q (Hcc _ Hin)). }
      pose proof (caller_given env wf declared ps m (Intersection cs) Hc) as Hc'. fold k in Hc'. rewrite EC in Hc'.
      destruct (instance_ground _ Hc') as [K' [Hb' _]]. destruct (inst_intersection env wf sigma K' Hsf _ (proj1 Hc') Hb') as [E1 _].
      destruct (instance_ground _ Hc) as [K [Hb _]]. destruct (inst_intersection env wf sigma K Hsf cs Hcs Hb) as [E0 Hall0].
      fold k. rewrite EC, E1, E0.
      set (c0 := common_mutability env (map (instantiate env sigma) cs)).
      set (J := intersect_mutability (mutability_of env (Intersection (map (with_mutability env c0) (map (instantiate env sigma) cs)))) m).
      cbn [with_mutability]. fold J.
      set (c1 := common_mutability env (map (instantiate env sigma) (map (with_mutability env C) cs))).
      set (C' := fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env J c))
          (map (with_mutability env c0) (map (instantiate env sigma) cs))) readonly).
      assert (Ecl: forall c, In c cs -> is_class (instantiate env sigma c) = true) by (intros c Hin; exact (proj2 (Hall0 c Hin))).
      (* the mutability they take in common, either way *)
      assert (E01: c1 = C').
      { assert (Ec1: c1 = fold_left intersect_mutability (map (fun c => if top_const env (instantiate env sigma c) then exclusive
                else intersect_mutability (mutability_of env (instantiate env sigma c)) C) cs) readonly).
        { unfold c1, common_mutability. rewrite !map_map. f_equal. apply map_ext_in. intros c Hin. cbv beta.
          rewrite (Ecomp c Hin). exact (proj1 (class_with_mutability _ _ (Ecl c Hin))). }
        assert (EC': C' = fold_left intersect_mutability (map (fun c => if top_const env (instantiate env sigma c) then exclusive else J) cs)
            readonly).
        { unfold C'. rewrite !map_map. f_equal. apply map_ext_in. intros c Hin. cbv beta.
          rewrite with_mutability_twice. exact (proj1 (class_with_mutability _ _ (Ecl c Hin))). }
        rewrite Ec1, EC'.
        destruct (existsb (fun c => top_const env (instantiate env sigma c)) cs) eqn:Eex.
        - apply existsb_exists in Eex. destruct Eex as [cj [Hj Ej]].
          rewrite !fold_meet_exclusive; [reflexivity| |];
              apply in_map_iff; exists cj; (split; [rewrite Ej; reflexivity|exact Hj]).
        - assert (Hnc: forall c, In c cs -> top_const env (instantiate env sigma c) = false).
          { intros c Hin. destruct (top_const env (instantiate env sigma c)) eqn:E; [|reflexivity].
            assert (Ht: existsb (fun c => top_const env (instantiate env sigma c)) cs = true)
                by (apply existsb_exists; exists c; split; [exact Hin|exact E]).
            rewrite Ht in Eex. discriminate Eex. }
          assert (E1': fold_left intersect_mutability (map (fun c => if top_const env (instantiate env sigma c) then exclusive
                  else intersect_mutability (mutability_of env (instantiate env sigma c)) C) cs) readonly
              = fold_left intersect_mutability (map (fun c => intersect_mutability (mutability_of env (instantiate env sigma c)) C) cs) readonly)
              by (f_equal; apply map_ext_in; intros c Hin; rewrite (Hnc c Hin); reflexivity).
          assert (E2': fold_left intersect_mutability (map (fun c => if top_const env (instantiate env sigma c) then exclusive else J) cs) readonly
              = fold_left intersect_mutability (map (fun _ => J) cs) readonly)
              by (f_equal; apply map_ext_in; intros c Hin; rewrite (Hnc c Hin); reflexivity).
          rewrite E1', E2'.
          rewrite (fold_meet_cons _ C cs Hne), (fold_meet_const _ cs J Hne).
          set (F := fold_left intersect_mutability (map (fun c => mutability_of env (instantiate env sigma c)) cs) readonly).
          (* the instance mutability in common is F *)
          assert (Ec0: c0 = F).
          { unfold c0, F, common_mutability. rewrite map_map. f_equal. apply map_ext_in. intros c Hin.
            symmetry. exact (proj2 (proj2 (proj2 (class_with_mutability readonly _ (Ecl c Hin)))) (Hnc c Hin)). }
          assert (EJ: J = intersect_mutability F m).
          { unfold J. cbn [mutability_of].
            replace (existsb (top_const env) (map (with_mutability env c0) (map (instantiate env sigma) cs))) with false.
            - rewrite !map_map. rewrite (map_ext_in _ (fun _ => c0) cs).
              + rewrite (fold_meet_const _ cs c0 Hne), Ec0. reflexivity.
              + intros c Hin. rewrite (proj1 (proj2 (class_with_mutability c0 _ (Ecl c Hin)))), (Hnc c Hin). reflexivity.
            - symmetry. apply not_true_iff_false. intros Ht. apply existsb_exists in Ht. destruct Ht as [z [Hz Ez]].
              apply in_map_iff in Hz. destruct Hz as [z' [<- Hz']]. apply in_map_iff in Hz'. destruct Hz' as [c [<- Hin]].
              rewrite (proj1 (proj2 (proj2 (class_with_mutability c0 _ (Ecl c Hin))))), (Hnc c Hin) in Ez. discriminate Ez. }
          rewrite EJ. unfold C, k. destruct (existsb (top_const env) cs) eqn:Etc.
          + (* a component of a const bound: its instance, not const, is exclusive *)
            apply existsb_exists in Etc. destruct Etc as [cj [Hj Ej]].
            destruct (proj2 (Hmc cj Hj) Ej) as [Et|Ex]; [rewrite (Hnc cj Hj) in Et; discriminate Et|].
            assert (EF: F = exclusive) by (apply fold_meet_exclusive; apply in_map_iff; exists cj; split; [exact Ex|exact Hj]).
            rewrite EF. destruct m; reflexivity.
          + cbn [mutability_of]. rewrite Etc.
            assert (HFG: Model.is_subtype_of F (fold_left intersect_mutability (map (mutability_of env) cs) readonly) = true)
                by (apply fold_meet_monotone; [reflexivity|intros c Hin; exact (proj1 (Hmc c Hin) (Hnc c Hin))]).
            rewrite <- intersect_mutability_assoc, (intersect_below_eq _ _ HFG). reflexivity. }
      rewrite E01. f_equal. rewrite !map_map. apply map_ext_in. intros c Hin.
      rewrite (Ecomp c Hin), !with_mutability_twice. reflexivity. }
    intros m x Hc. destruct (wtfrag_cases env x (proj1 Hc)) as [Hwx|[[cs [-> Hcs]]|[cs [-> Hcs]]]].
    - exact (Hw m x Hc Hwx).
    - exact (Hint cs m Hc Hcs).
    - (* a nullable intersection: as the intersection, made nullable *)
      assert (HcI: caller (Intersection cs)) by (split; [exact Hcs|split; [exact I|exact (proj2 (proj2 Hc))]]).
      pose proof (Hint cs m HcI Hcs) as E.
      pose proof (rewrap_sigma (Intersection cs)) as ER. cbn [rewrap_nullable] in ER.
      change (with_mutability env (intersect_mutability (mutability_of env (Nullable (Intersection cs))) m) (Nullable (Intersection cs)))
          with (rewrap_nullable (with_mutability env (intersect_mutability (mutability_of env (Intersection cs)) m) (Intersection cs))).
      rewrite rewrap_sigma, E, ER, with_mutability_rewrap, mutability_rewrap. reflexivity.
Qed.

(* ... and so, narrowed or not, a type of generic code a reference to a type variable is bound to:
   instantiated, it is the instance, of the mutability given and narrowed *)
Lemma instance_ref_apply: forall gm nn x, of_fragment env declared x -> caller x ->
    instantiate env sigma (ref_apply env gm nn x) = ref_apply env gm nn (instantiate env sigma x).
Proof.
    intros gm nn x Hfx Hcx. unfold ref_apply. cbn zeta.
    assert (EW: instantiate env sigma (match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end)
        = match gm with Some m => with_mutability env (intersect_mutability (mutability_of env (instantiate env sigma x)) m)
            (instantiate env sigma x) | None => instantiate env sigma x end)
        by (destruct gm as [m|]; [exact (instance_given m x Hcx)|reflexivity]).
    destruct nn; [|exact EW]. rewrite <- EW.
    set (W := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end).
    assert (HfW: of_fragment env declared W) by exact (ref_apply_of_fragment env wf declared declared_wf gm false x Hfx).
    assert (HcW: caller W) by (unfold W; destruct gm as [m|]; [exact (caller_given env wf declared ps m x Hcx)|exact Hcx]).
    pose proof (caller_without_null env wf declared ps W HcW) as HcN.
    destruct (instance_ground _ HcN) as [KN [HbN HgN]].
    pose proof (proj1 (proj2 (inst_facts env wf sigma KN Hsf _ (proj1 HcN) HbN))
        (without_null_not_nullable env wf declared declared_wf W (proj1 HfW))) as HnN.
    rewrite <- (ground_non_null_without_null env _ HgN HnN).
    rewrite (without_null_nullable_assignee W (proj1 HfW)). exact (instance_nullable_assignee W (proj1 HfW) HcW).
Qed.

(* At run time, the type a variable stands for, of a mutability given to it or narrowed, takes what the
   type takes, where that fits the mutability and is non-null where it is narrowed *)
Lemma ground_given_target: forall f gm nn z a, ground env z = true -> ground env a = true ->
    unify env f z a (Ongoing []) = Some (Ongoing []) ->
    (forall m, gm = Some m -> Model.is_subtype_of (assignment_mutability env a) m = true) ->
    (nn = true -> is_nullable env a = false) ->
    exists f', unify env f' (ref_apply env gm nn z) a (Ongoing []) = Some (Ongoing []).
Proof.
    intros f gm nn z a Hz Ha H Hgm Hnn. pose proof (ground_gfrag env z Hz) as Gz. pose proof (ground_gfrag env a Ha) as Ga.
    pose proof (ground_ref_apply gm nn z Hz) as Gt.
    unfold ref_apply in Gt |- *. cbn zeta in Gt |- *.
    set (y := match gm with Some m => with_mutability env (intersect_mutability (mutability_of env z) m) z | None => z end) in Gt |- *.
    pose proof (accepted_mutability env wf declared declared_wf f z a [] Gz Ga H) as Haz.
    assert (Hy: gfrag env y = true /\ vle env y z
        /\ Model.is_subtype_of (assignment_mutability env a) (assignment_mutability env y) = true /\ is_nullable env y = is_nullable env z).
    { unfold y. destruct gm as [m|].
      - split; [exact (gfrag_with_mutability env wf declared declared_wf _ z Gz)|].
        split.
        + apply (applied_vle env wf declared declared_wf z (Some (intersect_mutability (mutability_of env z) m)) None Gz (gfrag_uniform env z Gz)).
          cbn [applied]. rewrite (assignment_with_mutability env wf declared declared_wf _ z Gz). destruct (top_const env z) eqn:Et.
          * rewrite (top_const_assigned_exclusive env ranked z Et). reflexivity.
          * rewrite (not_top_const env wf z Et). apply intersect_mutability_left.
        + split; [|exact (is_nullable_with_mutability env wf _ z)].
          rewrite (assignment_with_mutability env wf declared declared_wf _ z Gz). destruct (top_const env z) eqn:Et.
          * rewrite (top_const_assigned_exclusive env ranked z Et) in Haz. exact Haz.
          * apply intersect_mutability_greatest; [|exact (Hgm m eq_refl)].
            exact (mutability_subtype_trans _ _ _ Haz (assignment_mutability_below env ranked z)).
      - split; [exact Gz|]. split; [|split; [exact Haz|reflexivity]].
        exact (applied_vle env wf declared declared_wf z None None Gz (gfrag_uniform env z Gz) (mutability_is_subtype_of_refl _)). }
    destruct Hy as [Gy [Hv [Hma Hny]]].
    apply (ground_accepts env wf declared declared_wf terminates finite tame); [exact Gt|exact Ha|].
    destruct nn.
    - apply (target_ordered env wf declared declared_wf f z (without_null env y) a [] Gz (gfrag_without_null env y Gy) Ga
          (vle_narrow_left env wf declared declared_wf _ _ Hv)); [| |exact H].
      + rewrite (without_null_keeps_assignment_mutability env ranked). exact Hma.
      + intros _. exact (Hnn eq_refl).
    - apply (target_ordered env wf declared declared_wf f z y a [] Gz Gy Ga Hv Hma); [|exact H].
      intros En. rewrite Hny in En. exact (ground_non_null env f z a [] [] Hz Ha En H).
Qed.

(* ... and is taken by what takes the type *)
Lemma ground_given_assignee: forall f gm nn z a, ground env z = true -> ground env a = true ->
    unify env f a z (Ongoing []) = Some (Ongoing []) -> exists f', unify env f' a (ref_apply env gm nn z) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f gm nn z a Hz Ha H. apply (ground_accepts env wf declared declared_wf terminates finite tame);
        [exact Ha|exact (ground_ref_apply gm nn z Hz)|].
    exact (instance_assigned_never_fails env wf declared declared_wf f gm nn z a (ground_gfrag env z Hz) (ground_gfrag env a Ha) H).
Qed.

(*
 * At run time, what is below the instance of each of some types of generic code is below the instance
 * of their intersection, as ofComponents makes it: of each component of theirs, of the mutability they
 * are assigned as in common, and without null where one isn't nullable. Its own mutability is no more
 * than the instance of each component is assigned as, which is no more than the component is
 * (runtime_mutability); so it takes the instance of each component given the common mutability.
 *)
Lemma runtime_of_components: forall A ys, ground env A = true -> is_nullable env A = false ->
    2 <= length (flat_map intersected_components ys) ->
    (forall y, In y ys -> of_fragment env declared y /\ caller y
        /\ exists f, unify env f (instantiate env sigma y) A (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (instantiate env sigma (of_components env (flat_map intersected_components ys))) A (Ongoing [])
        = Some (Ongoing []).
Proof.
    intros A ys HgA HnA Hl Hys.
    pose proof (ground_of_fragment env declared A HgA) as HfA.
    (* each component: below its instance, through the type it is a component of *)
    assert (Hz: forall z, In z (flat_map intersected_components ys) -> of_fragment env declared z /\ caller z
        /\ exists f, unify env f (instantiate env sigma z) A (Ongoing []) = Some (Ongoing [])).
    { intros z Hz'. apply in_flat_map in Hz'. destruct Hz' as [y [Hy Hzy]]. destruct (Hys y Hy) as [Hfy [Hcy HAy]].
      assert (Hthr: forall z', of_fragment env declared z' -> caller z' -> below env y z' ->
          of_fragment env declared z' /\ caller z' /\ exists f, unify env f (instantiate env sigma z') A (Ongoing []) = Some (Ongoing [])).
      { intros z' Hfz Hcz Hb. split; [exact Hfz|]. split; [exact Hcz|].
        destruct (instance_ground y Hcy) as [_ [_ Gy]]. destruct (instance_ground z' Hcz) as [_ [_ Gz]].
        exact (rtrans A _ _ HgA Gy Gz HAy (subst_below y z' Hcy Hcz Hb)). }
      destruct (gfrag_cases env y (proj1 Hfy)) as [[m [c [args ->]]]|[[n [-> [Hn Hgn]]]|[[gm [nn [p [vs [-> _]]]]]|[ds ->]]]].
      - destruct Hzy as [<-|[]]. exact (conj Hfy (conj Hcy HAy)).
      - destruct n as [m c args|n'|g|me msg|v o n'|g|ds]; cbn [intersected_components] in Hzy;
            try (destruct Hzy as [<-|[]]; exact (conj Hfy (conj Hcy HAy))).
        apply in_map_iff in Hzy. destruct Hzy as [d [<- Hd]].
        destruct (intersection_gfrag env ds Hgn) as [_ Hds]. destruct (Hds d Hd) as [Hcd Hgd].
        assert (Hfd: of_fragment env declared (Nullable d)).
        { split; [|exact I]. change (non_null env d && gfrag env d = true). rewrite Hgd, andb_true_r.
          destruct d; first [exact Hcd|discriminate Hcd]. }
        apply Hthr; [exact Hfd|exact (caller_nullable_component env declared ps ds d Hcy Hd)|].
        destruct (intersection_below_component env wf declared declared_wf terminates finite tame ds d (conj Hgn I) Hd)
            as [f Hf].
        exists (S f). rewrite unify_nullable_nullable. exact Hf.
      - destruct Hzy as [<-|[]]. exact (conj Hfy (conj Hcy HAy)).
      - cbn [intersected_components] in Hzy.
        destruct (intersection_gfrag env ds (proj1 Hfy)) as [_ Hds]. destruct (Hds z Hzy) as [_ Hgz].
        apply Hthr; [exact (conj Hgz I)|exact (caller_component env declared ps ds z Hcy Hzy)|].
        exact (intersection_below_component env wf declared declared_wf terminates finite tame ds z Hfy Hzy). }
    remember (flat_map intersected_components ys) as zs eqn:Ezs. clear Ezs Hys.
    destruct zs as [|z1 [|z2 zs']]; [simpl in Hl; lia|simpl in Hl; lia|].
    set (m := fold_left intersect_mutability (map (assignment_mutability env) (z1 :: z2 :: zs')) readonly).
    (* the mutability the components are assigned as in common: no less than that of A *)
    assert (Hm: Model.is_subtype_of (assignment_mutability env A) m = true).
    { rewrite <- (fold_meet_const _ (z1 :: z2 :: zs') (assignment_mutability env A) ltac:(discriminate)). unfold m.
      apply fold_meet_monotone; [reflexivity|]. intros z Hin. destruct (Hz z Hin) as [Hfz [Hcz [f Hf]]].
      destruct (instance_ground z Hcz) as [_ [_ Gz]].
      exact (mutability_trans _ _ _ (ground_mutability env wf f _ _ [] [] Gz HgA Hf)
          (runtime_mutability z _ Hfz Hcz (mutability_is_subtype_of_refl _))). }
    (* given it, a component is the reference to it given the mutability *)
    assert (Ewm: forall (nn: bool) z, In z (z1 :: z2 :: zs') ->
        (if nn then with_mutability env m (without_null env z) else with_mutability env m z) = ref_apply env (Some m) nn z).
    { intros nn z Hin.
      assert (H1: Model.is_subtype_of m (assignment_mutability env z) = true)
          by (unfold m; apply fold_intersect_below_element; apply in_map; exact Hin).
      pose proof (mutability_trans _ _ _ H1 (assignment_mutability_below env ranked z)) as H2.
      assert (E: intersect_mutability (mutability_of env z) m = m).
      { replace (intersect_mutability (mutability_of env z) m) with (intersect_mutability m (mutability_of env z))
            by (destruct m, (mutability_of env z); reflexivity).
        exact (intersect_below_eq _ _ H2). }
      unfold ref_apply. cbn zeta beta iota. rewrite E. destruct nn.
      - exact (with_mutability_without_null env wf m z).
      - reflexivity. }
    assert (Hwz: forall (nn: bool) z, In z (z1 :: z2 :: zs') ->
        of_fragment env declared (instantiate env sigma (ref_apply env (Some m) nn z))
        /\ below env A (instantiate env sigma (ref_apply env (Some m) nn z))).
    { intros nn z Hin. destruct (Hz z Hin) as [Hfz [Hcz [f Hf]]]. destruct (instance_ground z Hcz) as [_ [_ Gz]].
      rewrite (instance_ref_apply (Some m) nn z Hfz Hcz).
      split; [exact (ground_of_fragment env declared _ (ground_ref_apply (Some m) nn _ Gz))|].
      apply (ground_given_target f (Some m) nn _ A Gz HgA Hf); [intros m' E; injection E as <-; exact Hm|intros _; exact HnA]. }
    assert (Hall: forall (nn: bool), forall y, In y (map (instantiate env sigma)
        (map (fun c => if nn then with_mutability env m (without_null env c) else with_mutability env m c) (z1 :: z2 :: zs'))) ->
        of_fragment env declared y /\ below env A y).
    { intros nn y Hy. rewrite map_map in Hy. apply in_map_iff in Hy. destruct Hy as [z [<- Hin]].
      rewrite (Ewm nn z Hin). exact (Hwz nn z Hin). }
    assert (Hlen: forall (nn: bool), 2 <= length (map (instantiate env sigma)
        (map (fun c => if nn then with_mutability env m (without_null env c) else with_mutability env m c) (z1 :: z2 :: zs'))))
        by (intros nn; rewrite !length_map; exact Hl).
    destruct (below_of_components env wf declared declared_wf terminates finite tame A _ HfA HnA (Hlen true) (Hall true))
        as [Hb [Hrw _]].
    destruct (below_of_components env wf declared declared_wf terminates finite tame A _ HfA HnA (Hlen false) (Hall false))
        as [Hb' _].
    assert (Hna: forall (nn: bool) y, In y (map (instantiate env sigma)
        (map (fun c => if nn then with_mutability env m (without_null env c) else with_mutability env m c) (z1 :: z2 :: zs'))) ->
        not_argument y = true)
        by (intros nn y Hy; destruct (Hall nn y Hy) as [[Hg _] _]; destruct y; first [reflexivity|discriminate Hg]).
    rewrite <- (intersect_instances_plain env _ (Hna true)) in Hb, Hrw.
    rewrite <- (intersect_instances_plain env _ (Hna false)) in Hb'.
    unfold of_components. cbv beta iota zeta. fold m.
    destruct (negb (forallb (is_nullable env) (z1 :: z2 :: zs'))); [exact Hb|].
    destruct (forallb is_nullable_type (z1 :: z2 :: zs')); [|exact Hb'].
    change (instantiate env sigma (Nullable (Intersection (map (fun c => with_mutability env m (without_null env c)) (z1 :: z2 :: zs')))))
        with (rewrap_nullable (instantiate env sigma (Intersection (map (fun c => with_mutability env m (without_null env c)) (z1 :: z2 :: zs'))))).
    exact Hrw.
Qed.

Lemma runtime_intersect_instances: forall A ys, ground env A = true -> is_nullable env A = false ->
    2 <= length (flat_map intersected_components ys) ->
    (forall y, In y ys -> of_fragment env declared y /\ caller y
        /\ exists f, unify env f (instantiate env sigma y) A (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (instantiate env sigma (intersect_instances env ys)) A (Ongoing []) = Some (Ongoing []).
Proof.
    intros A ys HgA HnA Hl Hys. rewrite intersect_instances_plain; [exact (runtime_of_components A ys HgA HnA Hl Hys)|].
    intros y Hy. destruct (Hys y Hy) as [[Hg _] _]. destruct y; first [reflexivity|discriminate Hg].
Qed.

Section Main.

(* The bindings of the callee at run time *)
Variable b: Bindings.
Variable K: nat.
Hypothesis Hb: forall p o z, lookup_binding b p = Some (TypeArgument Model.invariant o z) -> is_exact_ownership o = true /\ ground env z = true.
Hypothesis Hnv: nonnull_values env b.

Let Qa := caller_argument env declared ps.
Let yf := yfrag env declared caller b.
Let ayf := argument_yfrag env declared Qa b.

(* The types of the parameters, instantiated, are ground *)
Lemma instances_ground: forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> bound_in env b K [] (to_generic P) = true ->
        ground env (inst env b P) = true)
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> bound_in env b K [] (to_generic a) = true ->
        argument_gfrag env (instantiate env b a) = true /\ no_refs (instantiate env b a) = true).
Proof.
    induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[[m_bot ->]|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (proj2 (Hb p o x Ex)).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          ground env (inst env b (RootResolved m c args)) = true).
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)).
        assert (Hl: length args = length (parameter_ids env c)).
        { destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
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
      + intros [| | | |v o n| |] Hd Ha HbA; simpl in Ha; try discriminate Ha. simpl in Hd. change (nfrag env n = true) in Ha.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [_ Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn).
        assert (Hg: ground env (inst env b n) = true).
        { destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IHt n ltac:(lia) Ha' Hbn)|].
          (* a type variable narrowed, or made nullable: the type it is bound to, without null, or made nullable *)
          assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct Eq as [-> | ->]; exact Hbn).
          destruct (binds_ref_some env wf b K [] _ Hbq) as [o' [z [Ez _]]]. cbn [param_of] in Ez.
          destruct (inst_reference env b gm nn q [] _ _ _ Ez) as [Ei Ein]. pose proof (proj2 (Hb q o' z Ez)) as Hz.
          destruct Eq as [-> | ->]; [rewrite Ei|rewrite Ein; apply ground_rewrap_ground]; exact (ground_ref_apply gm nn z Hz). }
        unfold ground in Hg. apply andb_true_iff in Hg. exact Hg.
Qed.

Lemma instance_ground_b: forall P, ifrag env P = true -> bound_in env b K [] (to_generic P) = true ->
    ground env (inst env b P) = true.
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

Let gen := generic_arguments env wf declared declared_wf terminates finite tame intersect_in_fragment supertype_in_fragment
    intersect_below supertype_above caller Qa (caller_argument_nested env declared ps) (intersect_generic ps) (supertype_generic ps)
    caller_top' caller_bottom' (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
    (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b K Hnv.

Lemma yf_top: yf top_type.
Proof. exact (yfrag_top env wf declared caller caller_top' b). Qed.

Lemma yf_bottom: yf bottom_type.
Proof. exact (yfrag_bottom env wf declared caller caller_bottom' b). Qed.

Lemma instance_top: instantiate env sigma top_type = top_type.
Proof. reflexivity. Qed.

Lemma instance_bottom: instantiate env sigma bottom_type = bottom_type.
Proof. reflexivity. Qed.

(* A type variable narrowed or made nullable, in a type argument, at run time: as the target *)
Lemma rnested_target: forall n gm nn q P A s s' o z, sfrag env (Generic (mkGenericRef gm nn q [])) = true ->
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yf A -> gwf s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    lookup_binding b q = Some (TypeArgument Model.invariant o z) -> rsat b s' ->
    exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n gm nn q P A s s' o z Hsr EP HA Hs H Ez Hr.
    destruct (Hb q o z Ez) as [_ Hz].
    destruct (Hr q o z Ez) as [st' [Hl' Hfit]].
    assert (Hfits: forall st'', lookup_state s' q = Some st'' -> rfits st'' o z)
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    pose proof (ground_ref_apply gm nn z Hz) as HZ.
    (* the variable takes A0: the type it stands for does, of the mutability given to it, or narrowed *)
    assert (Hstep: forall k A0, yf A0 -> unify env (S k) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s) = Some (Ongoing s') ->
        exists f, unify env f (ref_apply env gm nn z) (instantiate env sigma A0) (Ongoing []) = Some (Ongoing [])).
    { intros k A0 HA0 H0.
      destruct (unify_variable_given env wf k gm nn q A0 s s' (shape_of_fragment A0 (proj1 (proj1 HA0))) H0) as [H1 [Hgm Hnul]].
      pose proof (proj2 (proj2 (proj2 HA0))) as HcA0.
      destruct (rtarget_leaf k q [] _ s s' Hs (proj1 HA0) (proj1 (proj2 HA0)) HcA0 H1 o z Hz Hfits) as [f Hf].
      destruct (instance_ground A0 HcA0) as [KA [HbA HgA]].
      apply (ground_given_target f gm nn z _ Hz HgA Hf).
      - intros m Em. apply (runtime_mutability A0 m (proj1 HA0) HcA0). pose proof (Hgm m Em) as Hm.
        destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? E0]]]|[[? [E0 _]]|[[? [? [? [? [E0 _]]]]]|[? E0]]]];
            subst A0; exact Hm.
      - intros En. subst nn. apply (proj1 (proj2 (inst_facts env wf sigma KA Hsf A0 (proj1 HcA0) HbA))).
        destruct (is_nullable env A0) eqn:EA; [|reflexivity].
        rewrite (narrowed_not_nullable env wf gm q Hsr) in Hnul. discriminate (Hnul eq_refl). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [f Hf]. exists f.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ez)). exact Hf.
    - (* made nullable: the variable takes the argument without null *)
      destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 (proj1 HA))) as [HgA0 _].
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps) b A HA)
          as HA0.
      destruct (Hstep n _ HA0 H) as [f Hf].
      destruct (instance_ground A (proj2 (proj2 (proj2 HA)))) as [_ [_ HgA]].
      destruct (instance_ground _ (proj2 (proj2 (proj2 HA0)))) as [_ [_ HgN]].
      rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ez)). exists (S f).
      rewrite (ground_rewrap env _ HZ), (ground_nullable_target env f _ _ [] HgA).
      rewrite <- (instance_nullable_assignee A (proj1 (proj1 HA)) (proj2 (proj2 (proj2 HA)))).
      exact (ground_unify_without_null env f _ _ [] [] HZ HgN Hf).
Qed.

(* ... and as the assignee *)
Lemma rnested_assignee: forall n gm nn q P A s s' o z,
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yf A -> gwf s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
    lookup_binding b q = Some (TypeArgument Model.invariant o z) -> rsat b s' ->
    exists f, unify env f (instantiate env sigma A) (inst env b P) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n gm nn q P A s s' o z EP HA Hs H Ez Hr.
    destruct (Hb q o z Ez) as [_ Hz].
    destruct (Hr q o z Ez) as [st' [Hl' Hfit]].
    assert (Hfits: forall st'', lookup_state s' q = Some st'' -> rfits st'' o z)
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    pose proof (ground_ref_apply gm nn z Hz) as HZ.
    (* what is assigned the variable is assigned the type it stands for, and so that of a mutability
       given to it, or narrowed *)
    assert (Hstep: forall k A0, yf A0 -> unify env (S k) A0 (TypeVariable (mkGenericRef gm nn q [])) (Ongoing s) = Some (Ongoing s') ->
        exists f, unify env f (instantiate env sigma A0) (ref_apply env gm nn z) (Ongoing []) = Some (Ongoing [])).
    { intros k A0 HA0 H0. rewrite (assignee_plain env k A0 gm nn q [] s (proj1 (proj1 HA0))) in H0.
      destruct (rassignee_leaf k q [] A0 s s' Hs (proj1 HA0) (proj2 (proj2 (proj2 HA0))) H0 o z Hz Hfits) as [f Hf].
      destruct (instance_ground A0 (proj2 (proj2 (proj2 HA0)))) as [_ [_ HgA0]].
      exact (ground_given_assignee f gm nn z _ Hz HgA0 Hf). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [f Hf]. exists f.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ez)). exact Hf.
    - destruct n as [|n]; [discriminate H|].
      destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [qa [ba [-> _]]]]]|[cs ->]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Han.
        destruct (Hstep n an Han H) as [f Hf].
        rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ez)).
        destruct (instance_ground an (proj2 (proj2 (proj2 Han)))) as [_ [_ HgAn]].
        change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
        rewrite (ground_rewrap env _ HgAn), (ground_rewrap env _ HZ). exists (S f). rewrite unify_nullable_nullable.
        exact (ground_unify_without_null env f _ _ [] [] HgAn HZ Hf).
      + rewrite step_generic_nullable in H. discriminate H.
      + rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
Qed.

(*
 * Inference is sound at run time: what unify accepts of an argument of generic code for a parameter,
 * the argument instantiated takes, with the type variables replaced by what they stand for at run
 * time (rsat): the type arguments, instantiated, of those bound exactly, and the instances of types of
 * generic code between their bounds.
 *)
Lemma runtime_arguments: forall n,
    (forall P A s s', ifrag env P = true -> args_narrowed env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', ifrag env P = true -> args_narrowed env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env sigma A) (inst env b P) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', argument_ifrag env P = true -> args_narrowed env P = true -> ayf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []))
    /\ (forall P A s s', argument_ifrag env P = true -> args_narrowed env P = true -> ayf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env sigma A) (instantiate env b P) (Ongoing []) = Some (Ongoing [])).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    destruct (gen n) as [Gt [Ga [Gat Gaa]]].
    (* the type of a type argument, also a type variable narrowed or made nullable *)
    assert (GHt: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A s s' HP Hn HA Hb' Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP Hsq]]]]];
          [destruct (Gt P A s s' HP' Hn HA Hb' Hs H) as [H1 [H2 _]]; exact (conj H1 H2)|].
      destruct (gnested_target env wf declared declared_wf terminates finite tame supertype_in_fragment supertype_above
          caller (supertype_generic ps) (caller_nullable env declared ps) (caller_narrowed env wf declared ps)
          b n gm nn q P A s s' Hsq EP HA Hs H) as [H1 [H2 _]]. exact (conj H1 H2). }
    assert (GHa: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yf A -> bound_in env b K [] (to_generic P) = true ->
        gwf s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A s s' HP Hn HA Hb' Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP _]]]]];
          [destruct (Ga P A s s' HP' Hn HA Hb' Hs H) as [H1 [H2 _]]; exact (conj H1 H2)|].
      destruct (gnested_assignee env wf declared declared_wf terminates finite tame intersect_in_fragment intersect_below
          caller (intersect_generic ps) (caller_nullable env declared ps)
          b n gm nn q P A s s' EP HA Hs H) as [H1 [H2 _]]. exact (conj H1 H2). }
    assert (IHnt: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yf A ->
        bound_in env b K [] (to_generic P) = true -> gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])).
    { intros P A s s' HP Hn HA Hb' Hs Hd H Hr.
      destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP Hsq]]]]]; [exact (IHt P A s s' HP' Hn HA Hb' Hs Hd H Hr)|].
      assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb').
      destruct (binds_ref_some env wf b K [] _ Hbq) as [o [z [Ez _]]]. cbn [param_of] in Ez.
      exact (rnested_target n gm nn q P A s s' o z Hsq EP HA Hs H Ez Hr). }
    assert (IHna: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yf A ->
        bound_in env b K [] (to_generic P) = true -> gwf s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        exists f, unify env f (instantiate env sigma A) (inst env b P) (Ongoing []) = Some (Ongoing [])).
    { intros P A s s' HP Hn HA Hb' Hs Hd H Hr.
      destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP _]]]]]; [exact (IHa P A s s' HP' Hn HA Hb' Hs Hd H Hr)|].
      assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb').
      destruct (binds_ref_some env wf b K [] _ Hbq) as [o [z [Ez _]]]. cbn [param_of] in Ez.
      exact (rnested_assignee n gm nn q P A s s' o z EP HA Hs H Ez Hr). }
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
      intros P A s s' HP Hn HA Hbp Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          args_narrowed env (RootResolved mt ct targs) = true ->
          yf (RootResolved ma ca aargs) -> caller (RootResolved ma ca aargs) ->
          bound_in env sigma KA [] (RootResolved ma ca aargs) = true ->
          bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (inst env b (RootResolved mt ct targs)) (instantiate env sigma (RootResolved ma ca aargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros mt ct targs ma ca aargs Hft Hnt Hfa Hca Hba Hbt Hu.
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
          destruct (Gat t a s0 s0' Hft' (args_narrowed_root env mt ct targs Hnt t Ht) Hya Hbt' Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. exact (IHat t a s0 s0' Hft' (args_narrowed_root env mt ct targs Hnt t Ht) Hya Hbt' Hs0 Hd0 E Hr0). }
        destruct (Hpairs targs norm s s' (instantiate env b) (instantiate env sigma) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes env wf P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP Hn HA HcA HbA Hbp H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          pose proof (yfrag_generic env wf declared declared_wf caller (caller_bound env wf declared ps) b _ HA) as Hyb.
          destruct (IHt _ _ s s' HP Hn Hyb Hbp Hs Hd H Hr) as [f1 E1].
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
          destruct (IHt _ _ s s' HP Hn Hyc Hbp Hs Hd Ec Hr) as [f1 E1].
          pose proof (proj2 (proj2 (proj2 Hyc))) as Hcc. destruct (instance_ground c Hcc) as [Kc [_ Hgc]].
          destruct (subst_below _ c HcA Hcc (intersection_below_component env wf declared declared_wf terminates finite
              tame cs c (proj1 HA) Hc)) as [f2 E2].
          exact (rtrans _ _ _ HgA Hgc (instance_ground_b _ HP Hbp) (ex_intro _ f2 E2) (ex_intro _ f1 E1)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hbp.
        pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps)
            (caller_narrowed env wf declared ps) b A HA) as HyN.
        destruct (IHt _ _ s s' HP' Hn HyN Hb' Hs Hd H Hr) as [f1 E1].
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
      intros P A s s' HP Hn HA Hbp Hs Hd H Hr.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA. destruct (instance_ground A HcA) as [KA [HbA HgA]].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          args_narrowed env (RootResolved mp cp pargs) = true ->
          yf (RootResolved ma ca aargs) ->
          bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          exists f, unify env f (instantiate env sigma (RootResolved ma ca aargs)) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing [])).
      { intros ma ca aargs mp cp pargs Hfp Hnp Hfa Hbp' Hu.
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
          { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables env wf b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        (* the type arguments, normalized: their type variables made nullable narrowed *)
        assert (Hnn: forall a, In a norm -> args_narrowed env a = true).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne].
          { rewrite class_eqb_refl. intros a Ha. exact (args_narrowed_root env mp cp pargs Hnp a Ha). }
          rewrite (class_eqb_false _ _ Hne). intros a Ha.
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          assert (Hny: forall y, In y pargs -> nullable_narrowed env y = true)
              by (change (forallb (nullable_narrowed env) pargs = true) in Hnp; apply forallb_forall, Hnp).
          assert (Hta: forall y, In y pargs -> is_type_argument y = true)
              by (intros y Hy; exact (proj1 (argument_ifrag_parts env y (proj1 (Hpargs y Hy))))).
          pose proof (supertype_arguments_narrowed env wf cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hta Hny a Ha) as E.
          destruct a as [|[| | | | | |]| | | | |]; try reflexivity; exact E. }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', gwf s0 -> dom b s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
            /\ (rsat b s0' -> exists f, unify env f (instantiate env sigma t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 Hd0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. pose proof (Haargs t Ht) as Hyt.
          destruct (Gaa a t s0 s0' Hfa' (Hnn a Ha) Hyt Hba' Hs0 E) as [Hs0' [Hm0 _]].
          split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n t a s0 s0' E)|].
          intros Hr0. exact (IHaa a t s0 s0' Hfa' (Hnn a Ha) Hyt Hba' Hs0 Hd0 E Hr0). }
        destruct (Hpairs aargs norm s s' (instantiate env sigma) (instantiate env b) Hp Hs Hd Hu Hr) as [f Hf].
        exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs),
            (assignment_mutability_of_class env ma ca (map (instantiate env sigma) aargs) aargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes env wf P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + pose proof (instance_ground_b _ HP Hbp) as HgP.
        destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP Hn HA Hbp H).
        * rewrite unify_nullable_class in H.
          pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Hyn.
          destruct (IHa _ _ s s' HP Hn Hyn Hbp Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in E1, HgP |- *.
          rewrite unify_nullable_class. exact (ground_unify_without_null env f1 _ _ [] [] HgN HgP E1).
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          injection H as <-. apply andb_true_iff in Ec. destruct Ec as [Ec _]. cbn [is_non_nullable_nothing] in Ec.
          destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [Hcn _]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          -- injection Heq as <- <- <-. rewrite Ec in Hcn. discriminate Hcn.
          -- rewrite Heq. exact (ground_takes_bottom _ _ HgA).
        * (* an intersection: each of its components takes it *)
          rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H.
          destruct (no_vars_filter cs (gfrag_components_no_vars env cs (proj1 (proj1 HA)))) as [Hvar Hnonvar].
          rewrite Hvar, Hnonvar in H. cbn zeta in H.
          set (Pc := RootResolved mp cp pargs) in *.
          destruct (fold_unify (fun inner component => unify env n component Pc inner) cs (Ongoing s)) as [[s2|]|] eqn:E1; try discriminate H.
          assert (Hstep: forall c, In c cs -> forall s0 s0', gwf s0 -> dom b s0 -> unify env n c Pc (Ongoing s0) = Some (Ongoing s0') ->
              gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
              /\ (rsat b s0' -> exists f, unify env f (instantiate env sigma c) (inst env b Pc) (Ongoing []) = Some (Ongoing []))).
          { intros c Hc s0 s0' Hs0 Hd0 E. destruct (yfrag_component env declared caller (caller_component env declared ps) b cs c HA Hc) as [Hyc _].
            destruct (Ga Pc c s0 s0' HP Hn Hyc Hbp Hs0 E) as [Hs0' [Hm0 _]].
            split; [exact Hs0'|]. split; [exact Hm0|]. split; [exact (unify_keeps_exact env n c Pc s0 s0' E)|].
            intros Hr0. exact (IHa Pc c s0 s0' HP Hn Hyc Hbp Hs0 Hd0 E Hr0). }
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
          apply (ground_accepts env wf declared declared_wf terminates finite tame _ _ HgA HgP).
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
          destruct (IHa _ _ s s' HP' Hn Hyn Hb' Hs Hd H Hr) as [f1 E1].
          destruct (instance_ground an (proj2 (proj2 (proj2 Hyn)))) as [Kn [_ HgN]].
          pose proof (instance_ground_b _ HP' Hb') as HgPn.
          exists (S f1). change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
          rewrite (ground_rewrap env _ HgN). rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in E1, HgPn.
          rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)), unify_nullable_nullable.
          exact (ground_unify_without_null env f1 _ _ [] [] HgN HgPn E1).
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
      + (* a type variable *)
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hbp) as [o [z [Ez _]]]. cbn [param_of] in Ez.
        destruct (Hr p o z Ez) as [st' [Hl' Hf']].
        rewrite (inst_variable env b p bnd _ _ _ Ez).
        apply (rassignee_leaf n p bnd A s s' Hs (proj1 HA) HcA H o z (proj2 (Hb p o z Ez))).
        intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP Hn HA Hbp Hs Hd H Hr; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      pose proof (narrowed_content env _ _ _ Hn) as Hnn.
      destruct (proj2 (proj2 (proj2 (proj2 HA)))) as [HcN [Hmq _]].
      destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hbp) as [Hob Hbn].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na
          (not_capturable env (of_fragment env declared) (of_fragment env declared) s nt (proj1 Hs))) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      destruct (instance_of_argument va oa na HcN Hmq) as [EA HgN].
      pose proof (ownership_runtime oa ot Ho Hoa Hob) as Hown.
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (nfrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) (instantiate env sigma na) [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (instantiate env sigma (TypeArgument va oa na)) (Ongoing [])
              = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn), EA.
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va _ (instantiate env sigma na) [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (GHt nt na s s1 HP Hnn HAn Hbn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n nt na s s1 E1) as Hk1. pose proof (dom_forward b s s1 Hs Hk1 Hd) as Hd1.
           destruct (GHa nt na s1 s' HP Hnn HAn Hbn Hs1 H) as [_ Hm2]. pose proof (unify_keeps_exact env n na nt s1 s' H) as Hk2.
           destruct (IHna nt na s1 s' HP Hnn HAn Hbn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHnt nt na s s1 HP Hnn HAn Hbn Hs Hd E1 (rsat_back b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHnt nt na s s' HP Hnn HAn Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHna nt na s s' HP Hnn HAn Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHnt nt top_type s s' HP Hnn yf_top Hbn Hs Hd H Hr) as [f Hf]
          | destruct (IHna nt bottom_type s s' HP Hnn yf_bottom Hbn Hs Hd H Hr) as [f Hf] ];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP Hn HA Hbp Hs Hd H Hr; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument env declared caller Qa (caller_argument_nested env declared ps) b va oa na HA) as [HAn Hoa].
      pose proof (narrowed_content env _ _ _ Hn) as Hnn.
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
           destruct (GHa np na s s1 HP Hnn HAn Hbn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n na np s s1 E1) as Hk1. pose proof (dom_forward b s s1 Hs Hk1 Hd) as Hd1.
           destruct (GHt np na s1 s' HP Hnn HAn Hbn Hs1 H) as [_ Hm2]. pose proof (unify_keeps_exact env n np na s1 s' H) as Hk2.
           destruct (IHnt np na s1 s' HP Hnn HAn Hbn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHna np na s s1 HP Hnn HAn Hbn Hs Hd E1 (rsat_back b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHna np na s s' HP Hnn HAn Hbn Hs Hd H Hr) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHnt np na s s' HP Hnn HAn Hbn Hs Hd H Hr) as [f Hf];
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
Lemma runtime_parameter: forall n P A s s', pfrag env P = true -> args_narrowed env P = true -> yf A ->
    bound_in env b K [] (pgeneric P) = true -> gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
    exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n P A s s' HP Hn HA Hbp Hs Hd H Hr.
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsr _]]]]]|[gm [nn [p [-> [Hsr _]]]]]]].
    { rewrite (pgeneric_ifrag env wf P HP') in Hbp. exact (proj1 (runtime_arguments n) P A s s' HP' Hn HA Hbp Hs Hd H Hr). }
    all: destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hbp) as [o [z [Ez _]]]; cbn [param_of] in Ez.
    - exact (rnested_target n gm nn p _ A s s' o z Hsr (or_introl eq_refl) HA Hs H Ez Hr).
    - exact (rnested_target n gm nn p _ A s s' o z Hsr (or_intror eq_refl) HA Hs H Ez Hr).
Qed.

(* An intersection as the type of a parameter, at run time: the instance of each component takes the
   argument A, instantiated; as rstatic_components, the components as they are, a type variable among
   them as rnested_target has it *)
Lemma rparam_components: forall n cs A s s', (forall C, In C cs -> compfrag env C = true) ->
    components_sfrag env (map to_generic cs) = true -> (forall C, In C cs -> args_narrowed env C = true) ->
    yf A -> bound_in env b K [] (Intersection (map to_generic cs)) = true -> gwf s -> dom b s ->
    unify env n (Intersection cs) A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
    forall C, In C cs -> exists f, unify env f (inst env b C) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n cs A s s' HSi Hcs Hcn HA Hbi Hs Hd H.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])))
        by (intros C HC; exact (param_component_cases env wf cs C HSi Hcs HC)).
    assert (HbC: forall C, In C cs -> bound_in env b K [] (to_generic C) = true)
        by (intros C HC; exact (bound_in_component env b K [] _ _ Hbi (in_map _ _ _ HC))).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    pose proof HA as [Ha [Hba [Hoa Hqa]]].
    destruct (instance_ground A Hqa) as [KA [_ HgA]].
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match A with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists an, A = Nullable an).
    { destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[an [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[an Ean]].
    2:{ assert (Hin: is_nullable env (Intersection cs) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (C0 :: cs0) C0 (or_introl eq_refl)).
          destruct (Hcsf _ (in_map to_generic (C0 :: cs0) C0 (or_introl eq_refl))) as [Hsh _]. unfold is_component_shape in Hsh.
          apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [reflexivity|exact Hsh]. }
        subst A. rewrite (unify_not_nullable_intersection env n1 cs _ s Hin) in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body env _ _ _ A s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    set (Q := fun x => exists f, unify env f (inst env b x) (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])).
    (* the components that aren't type variables: types of the parameters *)
    assert (Hns: forall x, In x ns -> forall s0 s0', gwf s0 -> dom b s0 -> unify env n1 x A (Ongoing s0) = Some (Ongoing s0') ->
        gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat b s0' -> Q x)).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      pose proof (compfrag_ifrag env x (HSi x Hx) Hv) as Hxi.
      destruct (proj1 (gen n1) x A s0 s0' Hxi (Hcn x Hx) HA (HbC x Hx) Hs0 E0) as [Hs0' [Hn0 _]].
      split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact (unify_keeps_exact env n1 _ A s0 s0' E0)|].
      intros Hr0. exact (proj1 (runtime_arguments n1) x A s0 s0' Hxi (Hcn x Hx) HA (HbC x Hx) Hs0 Hd0 E0 Hr0). }
    destruct (fold_unify (fun inner component => unify env n1 component A inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (rfold (fun x inner => unify env n1 x A inner) Q ns s s2 (fun x => unify_keeps_failure env n1 x A) Hns Hs Hd E2)
        as [Hs2 [Hd2 [_ [_ Hall2]]]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, gwf s3 /\ keeps_exact s2 s3 /\ (forall b', gsatisfies env declared b' s3 -> gsatisfies env declared b' s2)
        /\ yf na /\ below env A na
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component A inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component A (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of A, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Hd2 Ecov) as [Hs3 [Hn3 [Hk3 _]]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        destruct (Hcase cov Hcov) as [[mc [cl1 [argsc ->]]]|[gm [nn [q ->]]]]; [|discriminate Hv].
        destruct (root_takes env wf declared declared_wf n1 mc cl1 argsc A s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn' in H.
        set (m' := intersect_mutability (mutability_of env A) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': Model.is_subtype_of (assignment_mutability env A) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked A).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hk3|]. split; [exact Hn3|].
        split; [split; [exact (any_of_fragment env wf declared m')|]|].
        { split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
          split; [exact I|exact (caller_any env wf declared ps m')]. }
        split; [exact (below_any_of env wf declared declared_wf terminates finite tame _ _ Ha Hcn' Hm')|exact H].
      - (* nothing covers: the variables take A *)
        exists A, s2. split; [exact Hs2|]. split; [apply keeps_exact_refl|]. split; [auto|]. split; [exact HA|].
        split; [exact (below_refl env wf declared declared_wf terminates finite tame A Ha)|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hk3 [Hn3 [Hyna [Hcna Hfold]]]]]]].
    assert (Hvs: forall x, In x vs -> forall s0 s0', gwf s0 -> dom b s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x A (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat b s0' -> Q x)).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      destruct (Hcase x Hx) as [[m [cl [args EC]]]|[gm [nn [q EC]]]]; [rewrite EC in Hv; discriminate Hv|].
      pose proof (HbC x Hx) as HbCq. destruct (Hcsf _ (in_map to_generic _ _ Hx)) as [_ Hsq]. rewrite EC in HbCq, Hsq, E0 |- *.
      cbn [to_generic] in HbCq, Hsq.
      destruct n1 as [|n2]; [discriminate E0|].
      (* the variable takes A0, through which it takes A *)
      assert (Hone: forall A0, yf A0 ->
          (forall Z, ground env Z = true -> (exists f, unify env f Z (instantiate env sigma A0) (Ongoing []) = Some (Ongoing [])) ->
              exists f, unify env f Z (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])) ->
          unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s0) = Some (Ongoing s0') ->
          gwf s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
          /\ (rsat b s0' -> Q (TypeVariable (mkGenericRef gm nn q [])))).
      { intros A0 HA0 Hthr EA.
        destruct (unify_variable_given env wf n2 gm nn q A0 s0 s0' (shape_of_fragment A0 (proj1 (proj1 HA0))) EA) as [EA' _].
        destruct (gtarget_leaf env wf declared declared_wf terminates finite tame supertype_in_fragment supertype_above
            caller (supertype_generic ps) n2 q [] A0 s0 s0' Hs0 (proj1 HA0) (proj1 (proj2 HA0)) (proj2 (proj2 (proj2 HA0))) EA')
            as [Hs0' [Hn0 _]].
        split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact (unify_keeps_exact env (S n2) _ A0 s0 s0' EA)|].
        intros Hr0. destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbCq) as [o [z [Ez _]]]. cbn [param_of] in Ez.
        apply Hthr; [rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ez)); exact (ground_ref_apply gm nn z (proj2 (Hb q o z Ez)))|].
        exact (rnested_target (S n2) gm nn q _ A0 s0 s0' o z Hsq (or_introl eq_refl) HA0 Hs0 EA Ez Hr0). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena; try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. apply (Hone na Hyna); [|exact Ena].
        intros Z HZ [f1 E1]. destruct (subst_below A na Hqa (proj2 (proj2 (proj2 Hyna))) Hcna) as [f2 E2'].
        destruct (instance_ground na (proj2 (proj2 (proj2 Hyna)))) as [Kn [_ HgNa]].
        exact (rtrans _ _ _ HgA HgNa HZ (ex_intro _ f2 E2') (ex_intro _ f1 E1)).
      - exact (Hone A HA (fun Z _ E => E) E0). }
    destruct (rfold (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        Q vs s3 s') as [_ [_ [Hback3 [_ Hallv]]]].
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    { exact Hvs. }
    { exact Hs3. }
    { exact (dom_forward b s2 s3 Hs2 Hk3 Hd2). }
    { exact Hfold. }
    intros Hr C HC. pose proof (rsat_back b s2 s3 Hs2 Hk3 Hn3 Hd2 (Hback3 Hr)) as Hr2.
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
    - assert (Hin: In C ns) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]). exact (Hall2 Hr2 C Hin).
    - assert (Hin: In C vs) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]). exact (Hallv Hr C Hin).
Qed.

Let gpc := gparam_components env wf declared declared_wf terminates finite tame intersect_in_fragment supertype_in_fragment
    intersect_below supertype_above caller Qa (caller_argument_nested env declared ps) (intersect_generic ps) (supertype_generic ps)
    caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps)
    (caller_bound env wf declared ps) (caller_narrowed env wf declared ps) (caller_component env declared ps)
    (caller_supertype_arguments env wf declared ps) b K Hnv.

(* A parameter of any type of qfrag, at run time; of an intersection, nullable or not, as ofComponents
   makes the instance (below_of_components) *)
Lemma runtime_qparameter: forall n P A s s', qfrag env P = true -> args_narrowed env P = true -> yf A ->
    bound_in env b K [] (pgeneric P) = true -> gwf s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
    exists f, unify env f (inst env b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n P A s s' HQ Hn HA Hbp Hs Hd H Hr. destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]];
        [exact (runtime_parameter n P A s s' HP Hn HA Hbp Hs Hd H Hr)|].
    assert (Hcn: forall C, In C cs -> args_narrowed env C = true).
    { intros C HC. assert (E: forallb (nullable_narrowed env) cs = true) by (destruct EP as [-> | ->]; exact Hn).
      rewrite forallb_forall in E.
      destruct C as [m c args|[m c args|n'|g|me msg|v o n'|g|cs']|g|me msg|v o n'|g|cs']; try reflexivity; exact (E _ HC). }
    assert (HbI: bound_in env b K [] (Intersection (map to_generic cs)) = true) by (destruct EP as [-> | ->]; exact Hbp).
    destruct (components_sfrag_facts env _ Hcs) as [Hl Hcsf].
    (* below the instance of each component, below that of the intersection *)
    assert (Hinter: forall k A0, yf A0 -> unify env k (Intersection cs) A0 (Ongoing s) = Some (Ongoing s') -> rsat b s' ->
        ground env (inst_nested env b (Intersection (map to_generic cs))) = true
        /\ exists f, unify env f (inst_nested env b (Intersection (map to_generic cs))) (instantiate env sigma A0) (Ongoing [])
            = Some (Ongoing [])).
    { intros k A0 HA0 E Hr0.
      pose proof (rparam_components k cs A0 s s' HSi Hcs Hcn HA0 HbI Hs Hd E Hr0) as Hall.
      destruct (gpc k cs A0 s s' HSi Hcs Hcn HA0 HbI Hs E) as [_ [_ [HnA _]]].
      destruct (instance_ground A0 (proj2 (proj2 (proj2 HA0)))) as [KA [HbA HgA]].
      pose proof (proj1 (proj2 (inst_facts env wf sigma KA Hsf A0 (proj1 (proj2 (proj2 (proj2 HA0)))) HbA)) HnA) as HnsA.
      assert (Hys: forall y, In y (map (inst_nested env b) (map to_generic cs)) -> ground env y = true).
      { intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
        change (inst_nested env b (to_generic C)) with (inst env b C).
        destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
        - exact (instance_ground_b C (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity))
              (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC))).
        - pose proof (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC)) as HbC. rewrite EC in HbC |- *.
          destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbC) as [o [z [Ez _]]]. cbn [param_of] in Ez.
          rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ez)). exact (ground_ref_apply gm nn z (proj2 (Hb q o z Ez))). }
      change (inst_nested env b (Intersection (map to_generic cs)))
          with (of_components env (flat_map intersected_components (map (inst_component env b) (map to_generic cs)))).
      rewrite (map_ext_in (inst_component env b) (inst_nested env b) (map to_generic cs))
          by (intros c Hc; exact (inst_component_nested env b c (proj1 (Hcsf c Hc)))).
      destruct (below_of_components env wf declared declared_wf terminates finite tame (instantiate env sigma A0)
          (map (inst_nested env b) (map to_generic cs)) (ground_of_fragment env declared _ HgA) HnsA
          ltac:(rewrite length_map; exact Hl)) as [Hbi [_ [Hfi _]]].
      { intros y Hy. split; [exact (ground_of_fragment env declared _ (Hys y Hy))|].
        apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
        exact (Hall C HC). }
      (* ground: no type parameter among them that may be null *)
      assert (Hnd: forall y, In y (map (inst_nested env b) (map to_generic cs)) -> is_nullable env y = true ->
          match y with Nullable _ => True | _ => False end).
      { intros y Hy Hny. pose proof (Hys y Hy) as Hgy.
        destruct (ground_cases env y Hgy) as [[? [? [? ->]]]|[[? [? [? ->]]]|[[ys' [-> _]]|[ys' [-> _]]]]];
            first [exact I|discriminate Hny|rewrite (ground_intersection_not_nullable env ys' (or_introl Hgy)) in Hny; discriminate Hny]. }
      split; [exact (ground_of_components _ Hys (proj1 (Hfi Hnd)))|exact Hbi]. }
    destruct EP as [-> | ->].
    - exact (proj2 (Hinter n A HA H Hr)).
    - (* nullable: the intersection takes the argument without null *)
      destruct n as [|n]; [discriminate H|]. rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct (Hinter n _ (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps)
          (caller_narrowed env wf declared ps) b A HA) H Hr) as [HgX [f Hf]].
      change (inst env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
      exact (runtime_nullable_variable A _ _ f (proj1 (proj1 HA)) (proj2 (proj2 (proj2 HA))) HgX HgX eq_refl Hf).
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

(* The type arguments of generic code are captured as those of class types *)
Lemma argument_gfrag_shape: forall y, argument_gfrag env y = true -> is_type_argument y = true /\ no_vars y = true
    /\ forall vy oy Y k s w, y = TypeArgument vy oy Y -> unify env k Y bottom_type (Ongoing s) = Some (Ongoing w) -> w = s.
Proof.
    intros y Hy. split; [exact (argument_gfrag_type_argument env y Hy)|]. split; [exact (argument_gfrag_no_vars env y Hy)|].
    intros vy oy Y k s w -> E. simpl in Hy. exact (gkeeps env wf k Y bottom_type s w Hy (bottom_gfrag env wf) E).
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

Let gtypes := generic_inference_types env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
    tame intersect_in_fragment supertype_in_fragment intersect_below supertype_above.

Let ginv := generic_invocation_sound env wf declared declared_wf terminates finite tame intersect_in_fragment
    supertype_in_fragment intersect_below supertype_above caller (caller_argument env declared ps) (caller_argument_nested env declared ps)
    (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
    (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps) (caller_component env declared ps)
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
    (* the bounds: the declared ones *)
    (forall p bound, In (p, bound) (cvars ++ ovars) -> to_generic bound = parameter_bound env p) ->
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
    (forall P, In P Ps -> qfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ owners_outside env (map fst (cvars ++ ovars)) A
        /\ caller A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs
        ++ map (fun v => (fst v, TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U (fst v))))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f (instantiate env sigma A) (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hdecl HQbounds HfR HcR Hrec
        Hfo Hno Hcl Hobj Hzs Hxx Hzb HPs HPn HAs Hfold b Hbdef P A HPA.
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
    destruct (refs_fuel env wf (of_fragment env declared) (of_fragment env declared) gtypes vars b0 Hbounds) as [K0 [HK0 HK0r]].
    { intros p bound Hin. exists ref, bound. split; [unfold b0; exact (lookup_map_vars vars _ p bound Hnd' Hin)|].
      split; [reflexivity|]. split; [exact (of_fragment_of_class env declared _ (Hbounds p bound Hin))|]. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (pgeneric P) = true).
    { intros P' HP'. apply (pbound_in_from_refs env wf vars _ _ P' (proj1 (HPs P' HP')) (proj2 (HPs P' HP')) HK0 HK0r).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    (* the bounds themselves, of the nullability of the declared ones *)
    assert (Hb0nn: nonnull_values env b0).
    { intros q o x E Hq. unfold b0 in E.
      destruct (lookup_map_pairs vars (fun v => TypeArgument Model.invariant ref (snd v)) q _ E) as [[q' bound] [Hin [Hf Ea]]].
      cbn [fst snd] in Hf, Ea. subst q'. injection Ea as _ ->.
      rewrite (is_nullable_generic env ranked), (effective_bound_plain env ranked), <- (Hdecl q bound Hin), (is_nullable_to_generic env) in Hq.
      exact Hq. }
    destruct (ginv nf Ps As u U b0 K0 Hb0nn Hwfu (fun P' HP' => conj (proj1 (HPs P' HP')) (Hb0 P' HP')) HPn
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
      pose proof (generic_final_value_fits env wf declared declared_wf terminates finite tame caller U p st2 ref HwfU HlU He2 Hff) as Hfit.
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
    { destruct (below_refl env wf declared declared_wf terminates finite tame D (ground_of_fragment env declared D HgD)) as [[|f] Ef];
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
    assert (Hlookup': forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ of_fragment env declared x /\ exists f, unify env f bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [Ho [Hx Hf]]]]]. exists o, x.
      split; [exact Hl'|]. split; [exact Ho|]. split; [exact (ground_of_fragment env declared x Hx)|exact Hf]. }
    destruct (refs_fuel env wf (of_fragment env declared) (of_fragment env declared) gtypes vars b Hbounds Hlookup') as [K [HK HKr]].
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true).
    { intros P' HP'. apply (pbound_in_from_refs env wf vars _ _ P' (proj1 (HPs P' HP')) (proj2 (HPs P' HP')) HK HKr).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
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
    (* the values of non-null bounds, within them, aren't null *)
    assert (Hnv: nonnull_values env b).
    { intros p o z Hpb Hpn. assert (Hin: exists bound, In (p, bound) vars).
      { rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
        - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
          rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
          simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
        - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (instantiate env sigma (final_value_of env U q))) p _ Hpb)
              as [_ Hin]. apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
          exists bound. apply in_or_app. right. exact Hin. }
      destruct Hin as [bound Hin]. destruct (Hlookup p bound Hin) as [o' [x [Hl' [_ [Hx Hbx]]]]]. rewrite Hl' in Hpb.
      injection Hpb as <- <-.
      exact (within_bound_not_nullable env wf declared declared_wf p bound x (Hdecl p bound Hin)
          (in_fragment_is_gfrag env _ (Hbounds p bound Hin)) (ground_gfrag env x Hx) Hbx Hpn). }
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
      destruct (generic_qparameter env wf declared declared_wf terminates finite tame intersect_in_fragment supertype_in_fragment
          intersect_below supertype_above caller (caller_argument env declared ps) (caller_argument_nested env declared ps)
          (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b K Hnv nf
          P' A' s1 s1' (proj1 (HPs P' HP')) (HPn P' HP') HyA (Hb P' HP') Hs1 E) as [Hs1' [Hm1 _]].
      split; [exact Hs1'|]. split; [exact Hm1|]. split; [exact (unify_keeps_exact env nf P' A' s1 s1' E)|].
      intros Hr. exact (runtime_qparameter b K Hbv Hnv nf P' A' s1 s1' (proj1 (HPs P' HP')) (HPn P' HP') HyA (Hb P' HP') Hs1 Hd1 E Hr).
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
(* types (runtime_mixed). Their references to Nothing take no type arguments (nothing_is_bottom).  *)
(* ---------------------------------------------------------------------------------------------- *)

Section Bounded.

Hypothesis supertype_bottom_only: closest_common_supertype_keeps_bottom_only env declared.

Let Qa := caller_argument env declared ps.
Let gw := gwf2 env declared caller.

Let gleaf (k: nat) (b: Bindings) := gleaf_all env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
    tame intersect_in_fragment supertype_in_fragment intersect_below supertype_above caller Qa
    (caller_argument_nested env declared ps) (intersect_generic ps) (supertype_generic ps) caller_top' caller_bottom'
    (caller_any env wf declared ps) (caller_root env declared ps) (caller_nullable env declared ps) (caller_bound env wf declared ps)
    (caller_narrowed env wf declared ps) (caller_component env declared ps) (caller_supertype_arguments env wf declared ps)
    caller_ref_apply' caller_rewrap' supertype_bottom_only k b.

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
      destruct (below_refl env wf declared declared_wf terminates finite tame X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K (proj2 Hc))).
      + destruct (subst_below A X HcA HcX (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; exact EX))) as [f1 E1].
        exact (rtrans _ _ _ HgA HgX Hz (ex_intro _ f1 E1) (ex_intro _ K Hc)).
      + destruct (below_bottom env wf declared declared_wf terminates finite tame X HfX) as [kb Eb].
        destruct (subst_below A bottom_type HcA caller_bottom'
            (Hgf bottom_type (bottom_of_fragment env wf declared) ltac:(exists kb; cbn [compare_variances]; exact Eb))) as [f1 E1].
        exact (rtrans _ _ _ HgA ground_bottom Hz (ex_intro _ f1 E1) (ground_takes_bottom _ z Hz)).
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
      destruct (below_refl env wf declared declared_wf terminates finite tame X HfX) as [kX EX].
      destruct vb.
      + apply (both_ways (unify env K) _ z []) in Hc; [|apply unify_keeps_failure|intros w E; exact (ground_keeps env wf K _ _ [] w HgX Hz E)].
        destruct (subst_below X A HcX HcA (Hgf X HfX ltac:(exists kX; cbn [compare_variances]; rewrite EX; exact EX)))
            as [f1 E1].
        exact (rtrans _ _ _ Hz HgX HgA (ex_intro _ K (proj1 Hc)) (ex_intro _ f1 E1)).
      + destruct (below_top env wf declared declared_wf terminates finite tame X HfX) as [kt Et].
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

Let gm (n: nat) := mixed_arguments env wf declared declared_wf terminates finite tame caller Qa
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

(* A type variable narrowed or made nullable narrowed, in a type argument, at run time: as the target *)
Lemma rmnested_target: forall n gm0 nn q P A s s', sfrag env (Generic (mkGenericRef gm0 nn q [])) = true ->
    (P = TypeVariable (mkGenericRef gm0 nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm0 nn q []))) ->
    mbinds b P -> yf A -> gw s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    exists f, unify env f (rinst b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n gm0 nn q P A s s' Hsr EP Hmb HA Hs H Hr.
    assert (Hmq: exists a, lookup_binding b q = Some a) by (destruct EP as [-> | ->]; exact Hmb).
    destruct Hmq as [a Ea]. destruct (Hpb q a Ea) as [Hl [o [x [-> Hy]]]].
    assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm0 nn q [])) = ref_apply env gm0 nn x)
        by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    destruct (Hbv q o x Ea) as [Hfx Hcx]. destruct (instance_ground x Hcx) as [_ [_ Hgx]].
    destruct (Hr q o x Ea) as [st' [Hl' Hfit]].
    assert (Hfits: forall st'', lookup_state s' q = Some st'' -> rfits st'' o (instantiate env sigma x))
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    pose proof (instance_ref_apply gm0 nn x Hfx Hcx) as EI.
    pose proof (ground_ref_apply gm0 nn _ Hgx) as HZ.
    assert (Er: forall t, rinst b (Nullable t) = rewrap_nullable (rinst b t)).
    { intros t. unfold rinst. change (instantiate_free env b (Nullable t)) with (rewrap_nullable (instantiate_free env b t)).
      exact (rewrap_sigma _). }

    (* the variable takes A0: the type it stands for does, of the mutability given to it, or narrowed *)
    assert (Hstep: forall k A0, yf A0 -> unify env (S k) (TypeVariable (mkGenericRef gm0 nn q [])) A0 (Ongoing s) = Some (Ongoing s') ->
        exists f, unify env f (ref_apply env gm0 nn (instantiate env sigma x)) (instantiate env sigma A0) (Ongoing []) = Some (Ongoing [])).
    { intros k A0 HA0 H0.
      destruct (unify_variable_given env wf k gm0 nn q A0 s s' (shape_of_fragment A0 (proj1 (proj1 HA0))) H0) as [H1 [Hgm Hnul]].
      pose proof (proj2 (proj2 (proj2 HA0))) as HcA0.
      destruct (rtarget_leaf2 k b q [] _ s s' Hs HA0 H1 o _ Hgx Hfits) as [f Hf].
      destruct (instance_ground A0 HcA0) as [KA [HbA HgA]].
      apply (ground_given_target f gm0 nn _ _ Hgx HgA Hf).
      - intros m Em. apply (runtime_mutability A0 m (proj1 HA0) HcA0). pose proof (Hgm m Em) as Hm.
        destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? E0]]]|[[? [E0 _]]|[[? [? [? [? [E0 _]]]]]|[? E0]]]];
            subst A0; exact Hm.
      - intros En. subst nn. apply (proj1 (proj2 (inst_facts env wf sigma KA Hsf A0 (proj1 HcA0) HbA))).
        destruct (is_nullable env A0) eqn:EA; [|reflexivity].
        rewrite (narrowed_not_nullable env wf gm0 q Hsr) in Hnul. discriminate (Hnul eq_refl). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [f Hf]. exists f.
      unfold rinst. rewrite Ei, EI. exact Hf.
    - (* made nullable: the variable takes the argument without null *)
      destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 (proj1 HA))) as [HgA0 _].
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      pose proof (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps) b A HA)
          as HA0.
      destruct (Hstep n _ HA0 H) as [f Hf].
      destruct (instance_ground A (proj2 (proj2 (proj2 HA)))) as [_ [_ HgA]].
      destruct (instance_ground _ (proj2 (proj2 (proj2 HA0)))) as [_ [_ HgN]].
      rewrite Er. unfold rinst. rewrite Ei, EI. exists (S f).
      rewrite (ground_rewrap env _ HZ), (ground_nullable_target env f _ _ [] HgA).
      rewrite <- (instance_nullable_assignee A (proj1 (proj1 HA)) (proj2 (proj2 (proj2 HA)))).
      exact (ground_unify_without_null env f _ _ [] [] HZ HgN Hf).
Qed.

(* ... and as the assignee *)
Lemma rmnested_assignee: forall n gm0 nn q P A s s',
    (P = TypeVariable (mkGenericRef gm0 nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm0 nn q []))) ->
    mbinds b P -> yf A -> gw s -> unify env n A P (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    exists f, unify env f (instantiate env sigma A) (rinst b P) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n gm0 nn q P A s s' EP Hmb HA Hs H Hr.
    assert (Hmq: exists a, lookup_binding b q = Some a) by (destruct EP as [-> | ->]; exact Hmb).
    destruct Hmq as [a Ea]. destruct (Hpb q a Ea) as [Hl [o [x [-> Hy]]]].
    assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm0 nn q [])) = ref_apply env gm0 nn x)
        by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
    destruct (Hbv q o x Ea) as [Hfx Hcx]. destruct (instance_ground x Hcx) as [_ [_ Hgx]].
    destruct (Hr q o x Ea) as [st' [Hl' Hfit]].
    assert (Hfits: forall st'', lookup_state s' q = Some st'' -> rfits st'' o (instantiate env sigma x))
        by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
    pose proof (instance_ref_apply gm0 nn x Hfx Hcx) as EI.
    pose proof (ground_ref_apply gm0 nn _ Hgx) as HZ.
    assert (Er: forall t, rinst b (Nullable t) = rewrap_nullable (rinst b t)).
    { intros t. unfold rinst. change (instantiate_free env b (Nullable t)) with (rewrap_nullable (instantiate_free env b t)).
      exact (rewrap_sigma _). }

    (* what is assigned the variable is assigned the type it stands for, and so that of a mutability
       given to it, or narrowed *)
    assert (Hstep: forall k A0, yf A0 -> unify env (S k) A0 (TypeVariable (mkGenericRef gm0 nn q [])) (Ongoing s) = Some (Ongoing s') ->
        exists f, unify env f (instantiate env sigma A0) (ref_apply env gm0 nn (instantiate env sigma x)) (Ongoing []) = Some (Ongoing [])).
    { intros k A0 HA0 H0. rewrite (assignee_plain env k A0 gm0 nn q [] s (proj1 (proj1 HA0))) in H0.
      destruct (rassignee_leaf2 k b q [] A0 s s' Hs HA0 H0 o _ Hgx Hfits) as [f Hf].
      destruct (instance_ground A0 (proj2 (proj2 (proj2 HA0)))) as [_ [_ HgA0]].
      exact (ground_given_assignee f gm0 nn _ _ Hgx HgA0 Hf). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [f Hf]. exists f.
      unfold rinst. rewrite Ei, EI. exact Hf.
    - destruct n as [|n]; [discriminate H|].
      destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [qa [ba [-> _]]]]]|[cs ->]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        pose proof (proj1 (yfrag_nullable env declared caller (caller_nullable env declared ps) b an HA)) as Han.
        destruct (Hstep n an Han H) as [f Hf].
        rewrite Er. unfold rinst. rewrite Ei, EI.
        destruct (instance_ground an (proj2 (proj2 (proj2 Han)))) as [_ [_ HgAn]].
        change (instantiate env sigma (Nullable an)) with (rewrap_nullable (instantiate env sigma an)).
        rewrite (ground_rewrap env _ HgAn), (ground_rewrap env _ HZ). exists (S f). rewrite unify_nullable_nullable.
        exact (ground_unify_without_null env f _ _ [] [] HgAn HZ Hf).
      + rewrite step_generic_nullable in H. discriminate H.
      + rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
Qed.

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
    (* the type of a type argument, also a type variable narrowed or made nullable narrowed *)
    assert (GMt: forall P A s s', mfrag env declared caller b P \/ mref env b P -> yf A -> gw s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gw s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A s s' [HP|HP] HA Hs H; [destruct (Gt P A s s' HP HA Hs H) as [H1 [H2 _]]; exact (conj H1 H2)|].
      destruct (mref_cases env b P HP) as [gm' [nn [q [Hsq EP]]]].
      destruct (mnested_target env wf declared declared_wf terminates finite tame caller (caller_nullable env declared ps)
          (caller_narrowed env wf declared ps) b Hpb gw n gm' nn q P A s s' (fun k _ => gleaf k b) Hsq
          ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HA Hs H) as [H1 [H2 _]].
      exact (conj H1 H2). }
    assert (GMa: forall P A s s', mfrag env declared caller b P \/ mref env b P -> yf A -> gw s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gw s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A s s' [HP|HP] HA Hs H; [destruct (Ga P A s s' HP HA Hs H) as [H1 [H2 _]]; exact (conj H1 H2)|].
      destruct (mref_cases env b P HP) as [gm' [nn [q [_ EP]]]].
      destruct (mnested_assignee env wf declared declared_wf terminates finite tame caller (caller_nullable env declared ps)
          b Hpb gw n gm' nn q P A s s' (fun k _ => gleaf k b) ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HA Hs H)
          as [H1 [H2 _]].
      exact (conj H1 H2). }
    assert (IHmt: forall P A s s', mfrag env declared caller b P \/ mref env b P -> caller (instantiate_free env b P) -> mbinds b P ->
        nothing_is_bottom P = true -> yf A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        rsat2 b s' -> exists f, unify env f (rinst b P) (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])).
    { intros P A s s' [HP|HP] HcP HmP HnP HA Hs Hd H Hr; [exact (IHt P A s s' HP HcP HmP HnP HA Hs Hd H Hr)|].
      destruct (mref_cases env b P HP) as [gm' [nn [q [Hsq EP]]]].
      exact (rmnested_target n gm' nn q P A s s' Hsq ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HmP HA Hs H Hr). }
    assert (IHma: forall P A s s', mfrag env declared caller b P \/ mref env b P -> caller (instantiate_free env b P) -> mbinds b P ->
        nothing_is_bottom P = true -> yf A -> gw s -> dom b s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        rsat2 b s' -> exists f, unify env f (instantiate env sigma A) (rinst b P) (Ongoing []) = Some (Ongoing [])).
    { intros P A s s' [HP|HP] HcP HmP HnP HA Hs Hd H Hr; [exact (IHa P A s s' HP HcP HmP HnP HA Hs Hd H Hr)|].
      destruct (mref_cases env b P HP) as [gm' [nn [q [_ EP]]]].
      exact (rmnested_assignee n gm' nn q P A s s' ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HmP HA Hs H Hr). }
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
              tame cs c (proj1 HA) Hc)) as [f2 E2].
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
            destruct (mixed_supertype_arguments env wf declared declared_wf caller caller_bottom' b Hpb Hbf cp ca pargs Hne Hcn' Hbase Hlp Hpargs)
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
          destruct pargs; simpl in Hb0; try discriminate Hb0.
          exact (ground_takes_bottom _ _ HgA).
        * (* an intersection: each of its components takes it *)
          rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H.
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
          apply (ground_accepts env wf declared declared_wf terminates finite tame _ _ HgA HgP).
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
        * rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
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
      { rewrite (free_argument env b vt ot nt Hpb (margument_nested env wf declared declared_wf caller b Hpb Hbf nt HP)), (free_plain_ownership b ot Hot).
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
           destruct (GMt nt na s s1 HP HAn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n nt na s s1 E1) as Hk1. pose proof (dom_forward2 b s s1 Hs Hk1 Hd) as Hd1.
           destruct (GMa nt na s1 s' HP HAn Hs1 H) as [_ Hm2]. pose proof (unify_keeps_exact env n na nt s1 s' H) as Hk2.
           destruct (IHma nt na s1 s' HP HcNt HmP HnP HAn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHmt nt na s s1 HP HcNt HmP HnP HAn Hs Hd E1 (rsat_back2 b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHmt nt na s s' HP HcNt HmP HnP HAn Hs Hd H Hr) as [f Hf]
          | destruct (IHma nt na s s' HP HcNt HmP HnP HAn Hs Hd H Hr) as [f Hf]
          | destruct (IHmt nt top_type s s' HP HcNt HmP HnP (yfrag_top env wf declared caller caller_top' b) Hs Hd H Hr) as [f Hf]
          | destruct (IHma nt bottom_type s s' HP HcNt HmP HnP (yfrag_bottom env wf declared caller caller_bottom' b) Hs Hd H Hr) as [f Hf] ];
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
      { rewrite (free_argument env b vp op np Hpb (margument_nested env wf declared declared_wf caller b Hpb Hbf np HP)), (free_plain_ownership b op Hop).
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
           destruct (GMa np na s s1 HP HAn Hs E1) as [Hs1 _].
           pose proof (unify_keeps_exact env n na np s s1 E1) as Hk1. pose proof (dom_forward2 b s s1 Hs Hk1 Hd) as Hd1.
           destruct (GMt np na s1 s' HP HAn Hs1 H) as [_ Hm2]. pose proof (unify_keeps_exact env n np na s1 s' H) as Hk2.
           destruct (IHmt np na s1 s' HP HcNp HmP HnP HAn Hs1 Hd1 H Hr) as [f2 Hf2].
           destruct (IHma np na s s1 HP HcNp HmP HnP HAn Hs Hd E1 (rsat_back2 b s1 s' Hs1 Hk2 Hm2 Hd1 Hr)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHma np na s s' HP HcNp HmP HnP HAn Hs Hd H Hr) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHmt np na s s' HP HcNp HmP HnP HAn Hs Hd H Hr) as [f Hf];
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

(* An intersection as the type of a parameter, at run time: the instance of each component takes the
   argument A, instantiated; as rparam_components, the components that aren't type variables mixed
   types (runtime_mixed), those that are as rmnested_target has them *)
Lemma rmparam_components: forall n cs A s s', (forall C, In C cs -> compfrag env C = true) ->
    components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> plain_owners C = true /\ args_narrowed env C = true) -> nonnull_values env b ->
    (forall C, In C cs -> vars_in (bound_b b) C = true) ->
    yf A -> gw s -> dom b s ->
    unify env n (Intersection cs) A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    forall C, In C cs -> exists f, unify env f (rinst b C) (instantiate env sigma A) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n cs A s s' HSi Hcs Hcn Hnb Hvb HA Hs Hd H.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])))
        by (intros C HC; exact (param_component_cases env wf cs C HSi Hcs HC)).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    pose proof HA as [Ha [Hba [Hoa Hqa]]].
    destruct (instance_ground A Hqa) as [KA [_ HgA]].
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match A with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists an, A = Nullable an).
    { destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[an [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[an Ean]].
    2:{ assert (Hin: is_nullable env (Intersection cs) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (C0 :: cs0) C0 (or_introl eq_refl)).
          destruct (Hcsf _ (in_map to_generic (C0 :: cs0) C0 (or_introl eq_refl))) as [Hsh _]. unfold is_component_shape in Hsh.
          apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gmc [nn [q ->]]]]; [reflexivity|exact Hsh]. }
        subst A. rewrite (unify_not_nullable_intersection env n1 cs _ s Hin) in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body env _ _ _ A s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    set (Q := fun x => exists f, unify env f (rinst b x) (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])).
    (* the components that aren't type variables: mixed types *)
    assert (Hns: forall x, In x ns -> forall s0 s0', gw s0 -> dom b s0 -> unify env n1 x A (Ongoing s0) = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> Q x)).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      pose proof (compfrag_ifrag env x (HSi x Hx) Hv) as Hxi. destruct (Hcn x Hx) as [Hox Hnx].
      pose proof (ifrag_mfrag env wf declared caller b x Hxi Hox Hnx Hnb) as Hmx.
      destruct (proj1 (gm n1) x A s0 s0' Hmx HA Hs0 E0) as [Hs0' [Hn0 _]].
      split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact (unify_keeps_exact env n1 _ A s0 s0' E0)|].
      intros Hr0. exact (proj1 (runtime_mixed n1) x A s0 s0' Hmx
          (free_caller env wf declared ps b Hpb (fun q o y E => proj2 (Hbv q o y E)) x Hxi Hox (Hvb x Hx))
          (vars_in_mbinds b x (Hvb x Hx)) (ifrag_nib env wf x Hxi) HA Hs0 Hd0 E0 Hr0). }
    destruct (fold_unify (fun inner component => unify env n1 component A inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (rfold2 b (fun x inner => unify env n1 x A inner) Q ns s s2 (fun x => unify_keeps_failure env n1 x A) Hns Hs Hd E2)
        as [Hs2 [Hd2 [_ [_ Hall2]]]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, gw s3 /\ keeps_exact s2 s3 /\ (forall b', gsatisfies env declared b' s3 -> gsatisfies env declared b' s2)
        /\ yf na /\ below env A na
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component A inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component A (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of A, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Hd2 Ecov) as [Hs3 [Hn3 [Hk3 _]]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        destruct (Hcase cov Hcov) as [[mc [cl1 [argsc ->]]]|[gmc [nn [q ->]]]]; [|discriminate Hv].
        destruct (root_takes env wf declared declared_wf n1 mc cl1 argsc A s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn' in H.
        set (m' := intersect_mutability (mutability_of env A) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': Model.is_subtype_of (assignment_mutability env A) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked A).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hk3|]. split; [exact Hn3|].
        split; [split; [exact (any_of_fragment env wf declared m')|]|].
        { split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
          split; [exact I|exact (caller_any env wf declared ps m')]. }
        split; [exact (below_any_of env wf declared declared_wf terminates finite tame _ _ Ha Hcn' Hm')|exact H].
      - (* nothing covers: the variables take A *)
        exists A, s2. split; [exact Hs2|]. split; [apply keeps_exact_refl|]. split; [auto|]. split; [exact HA|].
        split; [exact (below_refl env wf declared declared_wf terminates finite tame A Ha)|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hk3 [Hn3 [Hyna [Hcna Hfold]]]]]]].
    assert (Hvs: forall x, In x vs -> forall s0 s0', gw s0 -> dom b s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x A (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> Q x)).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      destruct (Hcase x Hx) as [[m [cl [args EC]]]|[gm' [nn [q EC]]]]; [rewrite EC in Hv; discriminate Hv|].
      destruct (Hcsf _ (in_map to_generic _ _ Hx)) as [_ Hsq]. pose proof (Hvb x Hx) as HvC.
      rewrite EC in Hsq, E0, HvC |- *. cbn [to_generic] in Hsq.
      destruct n1 as [|n2]; [discriminate E0|].
      (* the variable takes A0, through which it takes A *)
      assert (Hone: forall A0, yf A0 ->
          (forall Z, ground env Z = true -> (exists f, unify env f Z (instantiate env sigma A0) (Ongoing []) = Some (Ongoing [])) ->
              exists f, unify env f Z (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])) ->
          unify env (S n2) (TypeVariable (mkGenericRef gm' nn q [])) A0 (Ongoing s0) = Some (Ongoing s0') ->
          gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
          /\ (rsat2 b s0' -> Q (TypeVariable (mkGenericRef gm' nn q [])))).
      { intros A0 HA0 Hthr EA.
        destruct (unify_variable_given env wf n2 gm' nn q A0 s0 s0' (shape_of_fragment A0 (proj1 (proj1 HA0))) EA) as [EA' _].
        destruct (proj1 (gleaf n2 b) q [] A0 s0 s0' Hs0 HA0 EA') as [Hs0' [Hn0 _]].
        split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact (unify_keeps_exact env (S n2) _ A0 s0 s0' EA)|].
        intros Hr0. apply Hthr.
        - cbn [vars_in] in HvC. rewrite andb_true_r in HvC. unfold bound_b in HvC.
          destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate HvC]. destruct (Hpb q a Ea) as [Hl [o [y [-> Hy]]]].
          assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm' nn q [])) = ref_apply env gm' nn y)
              by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity).
          destruct (Hbv q o y Ea) as [Hfy Hcy]. unfold rinst. rewrite Ei, (instance_ref_apply gm' nn y Hfy Hcy).
          destruct (instance_ground y Hcy) as [_ [_ Gy]]. exact (ground_ref_apply gm' nn _ Gy).
        - exact (rmnested_target (S n2) gm' nn q _ A0 s0 s0' Hsq (or_introl eq_refl) (vars_in_mbinds b _ HvC) HA0 Hs0 EA Hr0). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef gm' nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena; try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. apply (Hone na Hyna); [|exact Ena].
        intros Z HZ [f1 E1]. destruct (subst_below A na Hqa (proj2 (proj2 (proj2 Hyna))) Hcna) as [f2 E2'].
        destruct (instance_ground na (proj2 (proj2 (proj2 Hyna)))) as [Kn [_ HgNa]].
        exact (rtrans _ _ _ HgA HgNa HZ (ex_intro _ f2 E2') (ex_intro _ f1 E1)).
      - exact (Hone A HA (fun Z _ E => E) E0). }
    destruct (rfold2 b (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        Q vs s3 s') as [_ [_ [Hback3 [_ Hallv]]]].
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    { exact Hvs. }
    { exact Hs3. }
    { exact (dom_forward2 b s2 s3 Hs2 Hk3 Hd2). }
    { exact Hfold. }
    intros Hr C HC. pose proof (rsat_back2 b s2 s3 Hs2 Hk3 Hn3 Hd2 (Hback3 Hr)) as Hr2.
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gmc [nn [q EC]]]].
    - assert (Hin: In C ns) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]). exact (Hall2 Hr2 C Hin).
    - assert (Hin: In C vs) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]). exact (Hallv Hr C Hin).
Qed.

End RuntimeMixed.

(* A parameter, also of a type variable made nullable, at run time *)
Lemma runtime_mparameter: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
    forall n P A s s', pfrag env P = true -> plain_owners P = true -> args_narrowed env P = true -> nonnull_values env b ->
    vars_in (bound_b b) P = true ->
    yfrag env declared caller b A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    exists f, unify env f (instantiate env sigma (instantiate_free env b P)) (instantiate env sigma A) (Ongoing [])
        = Some (Ongoing []).
Proof.
    intros b Hpb Hbv n P A s s' HP Ho Hn Hst Hv HA Hs Hd H Hr.
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsr _]]]]]|[gm [nn [p [-> [Hsr _]]]]]]].
    {
      exact (proj1 (runtime_mixed b Hpb Hbv n) P A s s' (ifrag_mfrag env wf declared caller b P HP' Ho Hn Hst)
          (free_caller env wf declared ps b Hpb (fun q o x E => proj2 (Hbv q o x E)) P HP' Ho Hv)
          (vars_in_mbinds b P Hv) (ifrag_nib env wf P HP') HA Hs Hd H Hr). }
    - exact (rmnested_target b Hpb Hbv n gm nn p _ A s s' Hsr (or_introl eq_refl) (vars_in_mbinds b _ Hv) HA Hs H Hr).
    - exact (rmnested_target b Hpb Hbv n gm nn p _ A s s' Hsr (or_intror eq_refl) (vars_in_mbinds b _ Hv) HA Hs H Hr).
Qed.

(* A type of the fragment has components *)
Lemma intersected_not_nil: forall y, gfrag env y = true -> intersected_components y <> [].
Proof.
    intros y Hy. destruct (gfrag_cases env y Hy) as [[? [? [? ->]]]|[[n [-> [_ Hgn]]]|[[? [? [? [? [-> _]]]]]|[ds ->]]]];
        try discriminate.
    - destruct n as [| | | | | |ds]; try discriminate. cbn [intersected_components].
      destruct (intersection_gfrag env ds Hgn) as [Hne _]. destruct ds; [contradiction|discriminate].
    - cbn [intersected_components]. exact (proj1 (intersection_gfrag env ds Hy)).
Qed.

Lemma flat_length: forall l, (forall y, In y l -> intersected_components y <> []) ->
    length l <= length (flat_map intersected_components l).
Proof.
    induction l as [|y l IH]; intros H; [simpl; lia|]. cbn [flat_map]. rewrite length_app.
    pose proof (IH (fun y' Hy' => H y' (or_intror Hy'))) as Hl. destruct (intersected_components y) as [|z zs] eqn:E.
    - exfalso. exact (H y (or_introl eq_refl) E).
    - simpl. lia.
Qed.

(* A parameter of any type of qfrag, at run time, also of an intersection, nullable or not, as
   ofComponents makes its instance (runtime_of_components) *)
Lemma runtime_mqparameter: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
    forall n P A s s', qfrag env P = true -> (forall C, In C (intersected_components P) -> plain_owners C = true) ->
    args_narrowed env P = true -> nonnull_values env b -> vars_in (bound_b b) P = true ->
    yfrag env declared caller b A -> gw s -> dom b s -> unify env n P A (Ongoing s) = Some (Ongoing s') -> rsat2 b s' ->
    exists f, unify env f (instantiate env sigma (instantiate_free env b P)) (instantiate env sigma A) (Ongoing [])
        = Some (Ongoing []).
Proof.
    intros b Hpb Hbv n P A s s' HQ Ho Hn Hst Hv HA Hs Hd H Hr.
    destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]].
    { exact (runtime_mparameter b Hpb Hbv n P A s s' HP
          (Ho P ltac:(rewrite (intersected_none P (pfrag_not_inter env P HP)); left; reflexivity)) Hn Hst Hv HA Hs Hd H Hr). }
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x)
        by (intros q o x E; exact (proj1 (Hbv q o x E))).
    assert (Hcn: forall C, In C cs -> plain_owners C = true /\ args_narrowed env C = true).
    { intros C HC.
      assert (E: forallb (nullable_narrowed env) cs = true) by (destruct EP as [-> | ->]; exact Hn).
      rewrite forallb_forall in E.
      split; [destruct EP as [-> | ->]; [exact (Ho C HC)|exact (Ho (Nullable C) (in_map Nullable _ _ HC))]|].
      destruct C as [m c args|[m c args|n'|g|me msg|v o n'|g|cs']|g|me msg|v o n'|g|cs']; try reflexivity; exact (E _ HC). }
    assert (Hvc: forall C, In C cs -> vars_in (bound_b b) C = true)
        by (intros C HC; destruct EP as [-> | ->]; cbn [vars_in] in Hv; rewrite forallb_forall in Hv; exact (Hv C HC)).
    destruct (components_sfrag_facts env _ Hcs) as [Hl Hcsf]. rewrite length_map in Hl.
    (* the instances of the components: types of generic code, of the fragment *)
    assert (Hy: forall C, In C cs -> of_fragment env declared (instantiate_free env b C) /\ caller (instantiate_free env b C)).
    { intros C HC. destruct (Hcn C HC) as [HoC HnC].
      destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      - pose proof (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) as HCi.
        split; [|exact (free_caller env wf declared ps b Hpb (fun q o y E => proj2 (Hbv q o y E)) C HCi HoC (Hvc C HC))].
        exact (mixed_of_fragment env wf declared declared_wf caller b Hpb Hbf C
            (ifrag_mfrag env wf declared caller b C HCi HoC HnC Hst) (vars_in_mbinds b C (Hvc C HC))).
      - pose proof (Hvc C HC) as HvT. rewrite EC in HvT |- *. cbn [vars_in] in HvT. rewrite andb_true_r in HvT.
        unfold bound_b in HvT. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate HvT].
        destruct (Hpb q a Ea) as [Hla [o [x [-> Hy]]]].
        assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])) = ref_apply env gm nn x)
            by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hla, Hy; reflexivity).
        rewrite Ei. destruct (Hbv q o x Ea) as [Hfx Hcx].
        exact (conj (ref_apply_of_fragment env wf declared declared_wf gm nn x Hfx) (caller_ref_apply env wf declared ps gm nn x Hcx)). }
    (* below the instance of each component, below that of the intersection *)
    assert (Hinter: forall k A0, yfrag env declared caller b A0 -> unify env k (Intersection cs) A0 (Ongoing s) = Some (Ongoing s') ->
        exists f, unify env f (instantiate env sigma (instantiate_free env b (Intersection cs))) (instantiate env sigma A0) (Ongoing [])
            = Some (Ongoing [])).
    { intros k A0 HA0 E.
      pose proof (rmparam_components b Hpb Hbv k cs A0 s s' HSi Hcs Hcn Hst Hvc HA0 Hs Hd E Hr) as Hall.
      destruct (mparam_components env wf declared declared_wf terminates finite tame caller Qa
          (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) b Hpb Hbf gw
          (gwf2_capturable env declared caller) k (fun j _ => gleaf j b) cs A0 s s' HSi Hcs
          Hcn Hst
          HA0 Hs E) as [_ [_ [HnA _]]].
      destruct (instance_ground A0 (proj2 (proj2 (proj2 HA0)))) as [KA [HbA HgA]].
      pose proof (proj1 (proj2 (inst_facts env wf sigma KA Hsf A0 (proj1 (proj2 (proj2 (proj2 HA0)))) HbA)) HnA) as HnsA.
      cbn [instantiate_free]. destruct (existsb (mentions_bound b) cs) eqn:Em.
      - apply (runtime_intersect_instances _ _ HgA HnsA).
        + apply (Nat.le_trans _ (length (map (instantiate_free env b) cs))); [rewrite length_map; exact Hl|].
          apply flat_length. intros y Hy'. apply in_map_iff in Hy'. destruct Hy' as [C [<- HC]].
          exact (intersected_not_nil _ (proj1 (proj1 (Hy C HC)))).
        + intros y Hy'. apply in_map_iff in Hy'. destruct Hy' as [C [<- HC]].
          split; [exact (proj1 (Hy C HC))|]. split; [exact (proj2 (Hy C HC))|exact (Hall C HC)].
      - (* it mentions nothing bound: closed class types, each as it is *)
        assert (Hcl: forall C, In C cs -> in_fragment env C = true /\ instantiate_free env b C = C).
        { intros C HC. destruct (Hcsf (to_generic C) (in_map _ _ _ HC)) as [_ HsfC].
          assert (EmC: mentions_bound b C = false).
          { destruct (mentions_bound b C) eqn:EmC; [|reflexivity].
            rewrite (proj2 (existsb_exists _ _) (ex_intro _ C (conj HC EmC))) in Em. discriminate Em. }
          pose proof (bound_unmentioned_closed b C (Hvc C HC) EmC) as Hnv.
          destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]];
              [|rewrite EC in Hnv; discriminate Hnv].
          pose proof (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) as HCi.
          pose proof (closed_of_ifrag env wf C HCi Hnv (proj1 (Hcn C HC))) as Hcl.
          rewrite (to_generic_closed C Hcl) in HsfC.
          destruct (proj1 (closed_facts env wf [] 0 [] _) C (le_n _) HsfC Hcl) as [Hfr _].
          split; [exact Hfr|exact (free_unmentioned env b Hpb C (in_fragment_is_gfrag env C Hfr) EmC)]. }
        change (instantiate env sigma (Intersection cs)) with (intersect_instances env (map (instantiate env sigma) cs)).
        rewrite intersect_instances_plain.
        2:{ intros y Hy'. apply in_map_iff in Hy'. destruct Hy' as [C [<- HC]].
            destruct (fragment_cases env C (proj1 (Hcl C HC))) as [[m [cl [args ->]]]|[m [cl [args [-> _]]]]]; reflexivity. }
        refine (proj1 (below_of_components env wf declared declared_wf terminates finite tame _ _
            (ground_of_fragment env declared _ HgA) HnsA _ _)).
        + rewrite length_map. exact Hl.
        + intros y Hy'. apply in_map_iff in Hy'. destruct Hy' as [C [<- HC]]. destruct (Hcl C HC) as [Hfr Eid].
          pose proof (Hall C HC) as HaC. unfold rinst in HaC. rewrite Eid in HaC.
          destruct (Hy C HC) as [_ HcC]. rewrite Eid in HcC. destruct (instance_ground C HcC) as [_ [_ GC]].
          split; [exact (ground_of_fragment env declared _ GC)|exact HaC]. }
    destruct EP as [-> | ->].
    - exact (Hinter n A HA H).
    - (* nullable: the intersection takes the argument without null *)
      destruct n as [|n]; [discriminate H|]. rewrite (nullable_target env n _ A s (proj1 (proj1 HA))) in H.
      destruct (Hinter n _ (yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps)
          (caller_narrowed env wf declared ps) b A HA) H) as [f Hf].
      change (instantiate_free env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate_free env b (Intersection cs))).
      rewrite rewrap_sigma.
      pose proof (proj2 (proj2 (proj2 HA))) as HcA.
      destruct (instance_ground A HcA) as [_ [_ GA]].
      assert (EN: instantiate env sigma (nullable_assignee env A) = nullable_assignee env (instantiate env sigma A)).
      { destruct (nullable_assignee_facts env wf declared declared_wf A (proj1 (proj1 HA))) as [HgN [HnN _]].
        pose proof (caller_nullable_assignee A (proj1 (proj1 HA)) HcA) as HcN.
        destruct (instance_ground _ HcN) as [KN [HbN GN]].
        pose proof (proj1 (proj2 (inst_facts env wf sigma KN Hsf _ (proj1 HcN) HbN)) HnN) as HnsN.
        rewrite <- (without_null_nullable_assignee _ (ground_gfrag env _ GA)), <- (instance_nullable_assignee A (proj1 (proj1 HA)) HcA).
        symmetry. exact (ground_non_null_without_null env _ GN HnsN). }
      rewrite EN in Hf.
      exact (nullable_below env wf declared declared_wf _ _ (ground_gfrag env _ GA) (ex_intro _ f Hf)).
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

Lemma nib_candidate: forall p c, of_fragment env declared c -> bottom_only env c = true ->
    forall S, ifrag env S = true -> nothing_is_bottom (with_candidate env p c S) = true.
Proof.
    intros p c Hfc Hbc. pose proof (proj1 Hfc) as Hgc. pose proof (bottom_only_nib c Hbc) as Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c Hgc).
    assert (Hpp: forall q a, lookup_binding [(p, TypeArgument Model.invariant ref c)] q = Some a -> is_loose a = false).
    { intros q a E. cbn [lookup_binding] in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hfinal: final_argument (TypeArgument Model.invariant ref c) = c).
    { unfold final_argument. cbn [is_loose Variance_beq negb orb]. rewrite Hcn. reflexivity. }
    assert (Hshape: forall n, ifrag env n = true -> nests_argument (with_candidate env p c n) = false).
    { intros n Hn. destruct (ifrag_cases env wf n Hn) as [[m [c' [args [-> _]]]]|[[m_bot ->]|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          try reflexivity.
      unfold with_candidate. cbn [instantiate lookup_binding]. destruct (param_eqb q p); [rewrite Hfinal; exact Hcn|reflexivity]. }
    fix IH 1. intros [m c' args|n|g|me msg|v o n|[gm nn q vs]|cs] HS; try discriminate HS.
    - pose proof (root_args_ifrag env wf m c' args HS) as Hargs.
      destruct (ifrag_cases env wf _ HS) as [[m' [c'' [args' [Heq [Hcn' _]]]]]|[[m_bot Heq]|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
          try discriminate Heq.
      + injection Heq as <- <- <-. unfold with_candidate. cbn [instantiate nothing_is_bottom]. rewrite Hcn'. cbn [andb].
        clear HS Hcn'.
        induction args as [|a args IHa]; [reflexivity|]. cbn [map forallb]. apply andb_true_iff.
        split; [|exact (IHa (fun a' Ha' => Hargs a' (or_intror Ha')))].
        pose proof (Hargs a (or_introl eq_refl)) as Ha.
        destruct a as [| | | |v o n| |]; try discriminate Ha.
        cbn [argument_ifrag] in Ha.
        destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]].
        2:{ destruct (Nat.eq_dec q p) as [->|Hq].
            { (* p itself: c, of the mutability given to it, narrowed or made nullable *)
              destruct (candidate_self env p c gm nn Hcn) as [E1 E2].
              pose proof (proj1 (ref_apply_of_fragment env wf declared declared_wf gm nn c Hfc)) as Hf'.
              pose proof (bottom_only_nib _ (bottom_only_ref_apply env wf declared declared_wf gm nn c Hfc Hbc)) as Hn'.
              assert (Hy: is_type_argument (instantiate env [(p, TypeArgument Model.invariant ref c)] n) = false
                  /\ (forall x, instantiate env [(p, TypeArgument Model.invariant ref c)] n = Nullable x -> is_type_argument x = false)
                  /\ nothing_is_bottom (instantiate env [(p, TypeArgument Model.invariant ref c)] n) = true).
              { unfold with_candidate in E1, E2. destruct Eq as [-> | ->]; [rewrite E1|rewrite E2].
                - destruct (gfrag_no_argument env _ Hf') as [H1 H2]. split; [exact H1|]. split; [exact H2|exact Hn'].
                - destruct (rewrap_no_argument env _ Hf') as [H1 H2]. split; [exact H1|]. split; [exact H2|].
                  destruct (ref_apply env gm nn c); exact Hn'. }
              destruct Hy as [Hy1 [Hy2 Hy3]].
              rewrite (instantiate_unloose_argument env _ v o n Hpp Hy1 Hy2). exact Hy3. }
            assert (En: instantiate env [(p, TypeArgument Model.invariant ref c)] n = n)
                by (destruct Eq as [-> | ->]; cbn [instantiate lookup_binding]; unfold param_eqb; rewrite (proj2 (Nat.eqb_neq q p) Hq); reflexivity).
            rewrite (instantiate_unloose_argument env _ v o n Hpp);
                [rewrite En; destruct Eq as [-> | ->]; reflexivity|rewrite En; destruct Eq as [-> | ->]; reflexivity
                |intros x Ex; rewrite En in Ex; destruct Eq as [-> | ->]; [discriminate Ex|injection Ex as <-; reflexivity]]. }
        clear Ha. rename Ha' into Ha.
        pose proof (Hshape n Ha) as Hns.
        rewrite (instantiate_unloose_argument env _ v o n Hpp).
        * cbn [nothing_is_bottom]. exact (IH n Ha).
        * unfold with_candidate in Hns. destruct (instantiate env _ n) as [| | | | | |]; try reflexivity; discriminate Hns.
        * intros x Ex. unfold with_candidate in Hns. rewrite Ex in Hns. destruct x; try reflexivity; discriminate Hns.
      + unfold bottom_type in Heq. injection Heq as -> -> ->. reflexivity.
    - assert (Hn: ifrag env n = true /\ exists m c' args, n = RootResolved m c' args).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[[m_bot Heq]|[[m [c' [args [Heq H']]]]|[? [Heq _]]]]];
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
        nonnull_values env b -> dom b s -> owners_free env b (lower_bound st) -> vars_in (fun q => param_eqb q p || bound_b b q) (static_upper_bound st) = true ->
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
    intros s s' p st Hm H Hnn Hnv b Hpb Hbv Hnb Hd Ho Hv Hr. destruct (Hm b Hd Hr) as [Hd' Hr'].
    exact (H Hnn Hnv b Hpb Hbv Hnb Hd' Ho Hv Hr').
Qed.

Let gwhole := gstatic_whole env wf declared declared_wf terminates finite tame caller Qa
    (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
    (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
    (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) caller_ref_apply' caller_rewrap'.

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
    (forall C, In C cs -> compfrag env C = true /\ bplain env p C = true /\ forall g, C = TypeVariable g -> param_of g <> p) ->
    components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    of_fragment env declared c -> bottom_only env c = true -> caller c ->
    (forall b, owners_free env b c -> yfrag env declared caller b a) ->
    (is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env a = false -> is_nullable env c = false) -> gw s ->
    unify env n (with_candidate env p c (Intersection cs)) a (Ongoing s) = Some (Ongoing s') ->
    forall b, plain_values b ->
        (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
        nonnull_values env b ->
        owners_free env b c -> vars_in (fun q => param_eqb q p || bound_b b q) (Intersection cs) = true -> dom b s -> rsat2 b s' ->
        forall C, In C cs ->
        exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p cs c a s s' Hcomp Hcs Hunif Hc Hbc Hqc Hya Hcnull Hs H b Hpb Hbv Hnb Hob Hvb Hd Hr.
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x)
        by (intros q o x E; exact (proj1 (Hbv q o x E))).
    assert (Hycb: yfrag env declared caller b c) by (split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars env declared c Hc) as Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c (proj1 Hc)).
    pose proof (Hya b Hob) as Hyab. destruct Hyab as [Ha [Hba [Hoa Hqa]]]. pose proof (Hya b Hob) as Hyab.
    assert (Haa: assignee_mutability env a = assignment_mutability env a)
        by (destruct (gfrag_cases env a (proj1 Ha)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; reflexivity).
    (* a component that is a type of the parameters, with c in place of p: mixed, its instance of generic code *)
    assert (Hone: forall C, ifrag env C = true -> bplain env p C = true -> (forall g, C = TypeVariable g -> param_of g <> p) ->
        vars_in (fun q => param_eqb q p || bound_b b q) C = true ->
        (is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env c = false) ->
        mfrag env declared caller b (with_candidate env p c C) /\ caller (instantiate_free env b (with_candidate env p c C))
        /\ mbinds b (with_candidate env p c C) /\ nothing_is_bottom (with_candidate env p c C) = true).
    { intros C HCi HCo HCt HvC Hcc. destruct (bplain_parts env p C HCo) as [HCo' HCn].
      split; [exact (mfrag_candidate env wf declared declared_wf caller caller_ref_apply' caller_rewrap' b p c Hycb Hnb Hcc C HCi HCo HCt)|].
      split; [|split; [exact (mbinds_candidate env wf b p c C HvC Hnc)|exact (nib_candidate p c Hc Hbc C HCi)]].
      rewrite (free_candidate env b p c C Hpb (proj1 Hc) (unmentioned env b c (proj1 Hc) Hob)
          (ref_apply_free env wf declared declared_wf b c Hpb Hc Hob) (ifrag_plain_variables env wf p C HCi HCo)).
      apply (free_caller env wf declared ps (with_value p c b)); [| |exact HCi|exact HCo'|].
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
    assert (HSi: forall C, In C cs -> compfrag env C = true) by (intros C HC; exact (proj1 (Hcomp C HC))).
    assert (Hnp: forall g, In (TypeVariable g) cs -> param_of g <> p)
        by (intros g Hg; exact (proj2 (proj2 (Hcomp _ Hg)) g eq_refl)).
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases env wf p cs C HSi Hcs Hnp HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    set (m0 := assignment_mutability env (Intersection cs)) in *.
    set (w := fun C => with_mutability env m0 (with_candidate env p c C)) in H.
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists cn, a = Nullable cn).
    { destruct (gfrag_cases env a (proj1 Ha)) as [[? [? [? ->]]]|[[cn [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[cn Ecn]].
    2:{ assert (Hwn: is_nullable env (Intersection (map w cs)) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (map w (C0 :: cs0)) (w C0) (or_introl eq_refl)).
          unfold w. rewrite (proj1 (proj2 (with_mutability_keeps env ranked _ _))).
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gm [nn [q [-> Hq]]]]].
          - unfold with_candidate. cbn [instantiate]. reflexivity.
          - rewrite (proj1 (candidate_reference env p c gm nn q Hq)). exact (Hnull _ (or_introl eq_refl)). }
        subst a. rewrite unify_step_once in H. unfold unify_step, unify_intersection in H. rewrite Hwn in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body env _ _ _ a s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) (map w cs)) in H.
    set (vs := filter is_type_variable (map w cs)) in H.
    destruct (instance_ground a Hqa) as [Kc [HbKc HgC]].
    (* the components that aren't type variables: the candidate in the bound, at run time *)
    assert (Hroot: forall C, In C cs -> is_type_variable (w C) = false -> forall s0 s0', gw s0 -> dom b s0 ->
        unify env n1 (w C) a (Ongoing s0) = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma a) (Ongoing [])
            = Some (Ongoing []))).
    { intros C HC Hv s0 s0' Hs0 Hd0 E0. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      2:{ unfold w in Hv. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)) in Hv. discriminate Hv. }
      assert (Ew: unify env n1 (w C) a (Ongoing s0) = unify env n1 (with_candidate env p c C) a (Ongoing s0)).
      { pose proof (Hunif C HC) as Hu. unfold w. rewrite EC in Hu |- *. unfold with_candidate.
        cbn [instantiate with_mutability]. apply (unify_root_mutability_any env wf declared declared_wf); [exact (proj1 Ha)|].
        cbn [assignment_mutability] in Hu |- *. destruct (is_const (declaration_of env cl)); [reflexivity|exact (eq_sym Hu)]. }
      rewrite Ew in E0. destruct (Hcomp C HC) as [HCf [HCo HCt]].
      pose proof (compfrag_ifrag env C HCf ltac:(rewrite EC; reflexivity)) as HCi.
      assert (Hcc: is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env c = false).
      { intros Hp. apply (Hcnull Hp). pose proof E0 as E0'. rewrite EC in E0'. unfold with_candidate in E0'. cbn [instantiate] in E0'.
        exact (proj1 (root_takes env wf declared declared_wf n1 _ _ _ a s0 s0' (proj1 Ha) E0')). }
      destruct (Hone C HCi HCo HCt (Hvcs C HC) Hcc) as [HmC [HcC [HbC HnC]]].
      destruct (proj1 (mixed_arguments env wf declared declared_wf terminates finite tame caller Qa
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
        /\ (na = a \/ is_nullable env a = false)
        /\ Model.is_subtype_of (assignee_mutability env a) (assignee_mutability env na) = true
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
        destruct (Hcase C1 HC1) as [[m1 [cl1 [args1 EC]]]|[gm [nn [q [EC Hq]]]]].
        2:{ subst cov. unfold w in Hv. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)) in Hv. discriminate Hv. }
        assert (Ecov': exists mc argsc, cov = RootResolved mc cl1 argsc).
        { subst cov. unfold w. rewrite EC. unfold with_candidate. cbn [instantiate with_mutability]. eauto. }
        destruct Ecov' as [mc [argsc ->]].
        destruct (root_takes env wf declared declared_wf n1 mc cl1 argsc a s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn' in H.
        set (m' := intersect_mutability (mutability_of env a) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': Model.is_subtype_of (assignment_mutability env a) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked a).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hk3|]. split; [exact Hn3|]. split; [exact (any_of_fragment env wf declared m')|].
        split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
        split; [exact (caller_any env wf declared ps m')|]. split; [exact I|].
        split; [exact (below_any_of env wf declared declared_wf terminates finite tame _ _ Ha Hcn' Hm')|].
        split; [right; exact Hcn'|]. split; [|exact H]. rewrite Haa. cbn [assignee_mutability assignment_mutability or_readonly].
        rewrite (wf_any_is_not_const env wf). exact Hm'.
      - (* nothing covers: the variables take c *)
        exists a, s2. split; [exact Hs2|]. split; [apply keeps_exact_refl|]. split; [auto|]. split; [exact Ha|].
        split; [exact Hba|]. split; [exact Hqa|]. split; [exact Hoa|].
        split; [exact (below_refl env wf declared declared_wf terminates finite tame a Ha)|]. split; [left; reflexivity|].
        split; [apply mutability_is_subtype_of_refl|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hk3 [Hn3 [Hfna [Hbna [Hqna [Hona [Hcna [Hnna [Hnam Hfold]]]]]]]]]]]].
    assert (Hyna: yfrag env declared caller b na) by (split; [exact Hfna|]; split; [exact Hbna|]; split; [exact Hona|exact Hqna]).
    destruct (instance_ground na Hqna) as [Kn [_ HgNa]].
    (* the type variables among the components: what they take, c is below, at run time *)
    assert (Hvs: forall x, In x vs -> forall s0 s0', gw s0 -> dom b s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x a (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
        /\ (rsat2 b s0' -> forall nn q, x = TypeVariable (mkGenericRef (Some m0) nn q []) ->
            (forall o y, lookup_binding b q = Some (TypeArgument Model.invariant o y) ->
                exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))
            /\ (nn = true -> is_nullable env a = false) /\ Model.is_subtype_of (assignee_mutability env a) m0 = true)).
    { intros x Hx s0 s0' Hs0 Hd0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      apply in_map_iff in Hx. destruct Hx as [C0 [EC0 HC0]].
      destruct (Hcase C0 HC0) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      { subst x. unfold w in Hv. rewrite EC in Hv. unfold with_candidate in Hv. cbn in Hv. discriminate Hv. }
      assert (Ex: x = TypeVariable (mkGenericRef (Some m0) nn q [])).
      { subst x. unfold w. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)). reflexivity. }
      rewrite Ex in E0 |- *. destruct n1 as [|n2]; [discriminate E0|].
      assert (Hone': forall A, yfrag env declared caller b A ->
          (forall z, ground env z = true -> (exists f, unify env f z (instantiate env sigma A) (Ongoing []) = Some (Ongoing [])) ->
              exists f, unify env f z (instantiate env sigma a) (Ongoing []) = Some (Ongoing [])) ->
          (A = a \/ is_nullable env a = false) ->
          Model.is_subtype_of (assignee_mutability env a) (assignee_mutability env A) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) A (Ongoing s0) = Some (Ongoing s0') ->
          gw s0' /\ (forall b', gsatisfies env declared b' s0' -> gsatisfies env declared b' s0) /\ keeps_exact s0 s0'
          /\ (rsat2 b s0' -> forall nn' q', TypeVariable (mkGenericRef (Some m0) nn q []) = TypeVariable (mkGenericRef (Some m0) nn' q' []) ->
              (forall o y, lookup_binding b q' = Some (TypeArgument Model.invariant o y) ->
                  exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))
              /\ (nn' = true -> is_nullable env a = false) /\ Model.is_subtype_of (assignee_mutability env a) m0 = true)).
      { intros A HA Hthr HAa HAm EA. pose proof (unify_keeps_exact env (S n2) _ A s0 s0' EA) as Hk0.
        destruct (unify_variable_given env wf n2 (Some m0) nn q A s0 s0' (shape_of_fragment A (proj1 (proj1 HA))) EA) as [EA' [HAg Hnul]].
        destruct (proj1 (gleaf n2 b) q [] A s0 s0' Hs0 HA EA') as [Hs0' [Hn0 _]].
        split; [exact Hs0'|]. split; [exact Hn0|]. split; [exact Hk0|].
        intros Hr0 nn' q' Eq. injection Eq as <- <-. split; [|split].
        - intros o y Ey. destruct (Hr0 q o y Ey) as [st' [Hl' Hf']].
          destruct (instance_ground y (proj2 (Hbv q o y Ey))) as [Ky [_ Hgy]].
          apply (Hthr _ Hgy). apply (rtarget_leaf2 n2 b q [] A s0 s0' Hs0 HA EA' o _ Hgy).
          intros st'' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hf'.
        - (* narrowed, the variable takes no nullable type *)
          intros ->. destruct HAa as [->|Ha']; [|exact Ha'].
          destruct (is_nullable env a) eqn:En; [|reflexivity].
          rewrite (narrowed_variable_not_nullable env wf declared declared_wf (Some m0) q) in Hnul. discriminate (Hnul eq_refl).
        - exact (mutability_subtype_trans _ _ _ HAm (HAg m0 eq_refl)). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena;
          try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. apply (Hone' na Hyna); [|exact Hnna|exact Hnam|exact Ena].
        intros z Hz [f1 E1]. destruct (subst_below a na Hqa Hqna Hcna) as [f2 E2'].
        exact (rtrans _ _ _ HgC HgNa Hz (ex_intro _ f2 E2') (ex_intro _ f1 E1)).
      - exact (Hone' a Hyab (fun z _ E => E) (or_introl eq_refl) (mutability_is_subtype_of_refl _) E0). }
    destruct (rfold2 b (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x a inner | r => r end)
        (fun x => forall nn q, x = TypeVariable (mkGenericRef (Some m0) nn q []) ->
            (forall o y, lookup_binding b q = Some (TypeArgument Model.invariant o y) ->
                exists f, unify env f (instantiate env sigma y) (instantiate env sigma a) (Ongoing []) = Some (Ongoing []))
            /\ (nn = true -> is_nullable env a = false) /\ Model.is_subtype_of (assignee_mutability env a) m0 = true)
        vs s3 s') as [_ [_ [Hback3 [_ Hallv]]]].
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    { intros x Hx s0 s0' Hs0 Hd0 E0. exact (Hvs x Hx s0 s0' Hs0 Hd0 E0). }
    { exact Hs3. }
    { exact (dom_forward2 b s2 s3 Hs2 Hk3 Hd2). }
    { exact Hfold. }
    pose proof (Hback3 Hr) as Hr3.
    pose proof (rsat_back2 b s2 s3 Hs2 Hk3 Hn3 Hd2 Hr3) as Hr2.
    intros C HC. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
    - (* a class type *)
      assert (Hv: is_type_variable (w C) = false) by (unfold w; rewrite EC; reflexivity).
      assert (Hin: In (w C) ns) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Hv; reflexivity]).
      unfold rinst.
      exact (Hall2 Hr2 (w C) Hin C HC eq_refl).
    - (* a type variable, of a mutability given to it or narrowed: the type it is bound to so *)
      assert (Ew: w C = TypeVariable (mkGenericRef (Some m0) nn q []))
          by (unfold w; rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)); reflexivity).
      assert (Hin: In (w C) vs) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Ew; reflexivity]).
      pose proof (Hvcs C HC) as HvC.
      rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)).
      rewrite EC in HvC. cbn [vars_in] in HvC. apply andb_true_iff in HvC. destruct HvC as [Hq' _].
      unfold param_eqb in Hq'. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hq'. cbn [orb] in Hq'. unfold bound_b in Hq'.
      destruct (lookup_binding b q) as [ab|] eqn:Ea; [|discriminate Hq'].
      destruct (Hpb q ab Ea) as [_ [o [y [-> _]]]].
      destruct (Hallv Hr (w C) Hin nn q Ew) as [Hz [Hann Ham]]. destruct (Hz o y Ea) as [f Hf].
      unfold rinst. rewrite (free_variable_any env b Hpb gm nn q [] o y Ea).
      destruct (Hbv q o y Ea) as [Hfy Hcy]. destruct (instance_ground y Hcy) as [_ [_ Hgy]].
      rewrite (instance_ref_apply gm nn y Hfy Hcy). apply (ground_given_target f gm nn _ _ Hgy HgC Hf).
      + (* the common mutability is no more than that given to it, at run time too *)
        intros m Em. apply (runtime_mutability a m Ha Hqa). rewrite <- Haa. apply (mutability_subtype_trans _ _ _ Ham).
        pose proof (proj1 (Hcomp C HC)) as HCf. pose proof (Hunif C HC) as Hu. fold m0 in Hu. rewrite <- Hu, EC.
        rewrite EC in HCf. exact (compfrag_given env wf gm nn q m HCf Em).
      + intros En. exact (proj1 (proj2 (inst_facts env wf sigma Kc Hsf a (proj1 Hqa) HbKc)) (Hann En)).
Qed.

Lemma rstatic_whole: forall n p S c s s', gstatic_form env p S ->
    of_fragment env declared c -> bottom_only env c = true -> caller c -> gw s ->
    unify env n (with_candidate env p c S) c (Ongoing s) = Some (Ongoing s') ->
    forall b, plain_values b ->
        (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x /\ caller x) ->
        nonnull_values env b ->
        owners_free env b c -> vars_in (fun q => param_eqb q p || bound_b b q) S = true -> dom b s -> rsat2 b s' ->
        forall C, In C (bound_components S) ->
        exists f, unify env f (rinst b (with_candidate env p c C)) (instantiate env sigma c) (Ongoing []) = Some (Ongoing []).
Proof.
    intros n p S c s s' [Hcomp [Hinter Hnl]] Hc Hbc Hqc Hs H b Hpb Hbv Hnb Hob Hvb Hd Hr.
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment env declared x)
        by (intros q o x E; exact (proj1 (Hbv q o x E))).
    assert (Hycb: yfrag env declared caller b c) by (split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars env declared c Hc) as Hnc.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c (proj1 Hc)).
    (* a component that is a type of the parameters, with c in place of p: mixed, its instance of generic code *)
    assert (Hone: forall C, ifrag env C = true -> bplain env p C = true -> (forall g, C = TypeVariable g -> param_of g <> p) ->
        vars_in (fun q => param_eqb q p || bound_b b q) C = true ->
        (is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env c = false) ->
        mfrag env declared caller b (with_candidate env p c C) /\ caller (instantiate_free env b (with_candidate env p c C))
        /\ mbinds b (with_candidate env p c C) /\ nothing_is_bottom (with_candidate env p c C) = true).
    { intros C HCi HCo HCt HvC Hcc. destruct (bplain_parts env p C HCo) as [HCo' HCn].
      split; [exact (mfrag_candidate env wf declared declared_wf caller caller_ref_apply' caller_rewrap' b p c Hycb Hnb Hcc C HCi HCo HCt)|].
      split; [|split; [exact (mbinds_candidate env wf b p c C HvC Hnc)|exact (nib_candidate p c Hc Hbc C HCi)]].
      rewrite (free_candidate env b p c C Hpb (proj1 Hc) (unmentioned env b c (proj1 Hc) Hob)
          (ref_apply_free env wf declared declared_wf b c Hpb Hc Hob) (ifrag_plain_variables env wf p C HCi HCo)).
      apply (free_caller env wf declared ps (with_value p c b)); [| |exact HCi|exact HCo'|].
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
    { rewrite E. intros C [<-|[]]. rewrite E in Hcomp. destruct (Hcomp S (or_introl eq_refl)) as [HCp [HCo HCt]].
      destruct (pfrag_cases env S HCp) as [HCi|[[gm [nn [q [ES _]]]]|[gm [nn [q [ES _]]]]]].
      - (* no intersection: as any other type of the parameters *)
        pose proof (fun g Eg => HCt g (or_introl Eg)) as HCt'.
        pose proof (fun Hp => ifrag_candidate_not_nullable env wf declared declared_wf n p c S c s s' HCi HCt' (proj1 Hc)
            (eq_trans (eq_sym Hnl) Hp) H) as Hcc.
        destruct (Hone S HCi HCo HCt' Hvb Hcc) as [HmC [HcC [HbC HnC]]].
        unfold rinst.
        exact (proj1 (runtime_mixed b Hpb Hbv n) _ c s s' HmC HcC HbC HnC Hycb Hs Hd H Hr).
      (* a type variable of a mutability given to it, narrowed or made nullable, other than p: as the type of a parameter *)
      - pose proof (HCt _ (or_introl ES)) as Hq. cbn [param_of] in Hq.
        assert (Ew: with_candidate env p c S = S) by (rewrite ES; exact (proj1 (candidate_reference env p c gm nn q Hq))).
        assert (Hvb': vars_in (bound_b b) S = true).
        { rewrite ES in Hvb |- *. cbn [vars_in] in Hvb |- *. rewrite andb_true_r in Hvb |- *.
          unfold param_eqb in Hvb. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hvb. exact Hvb. }
        rewrite Ew in H |- *. exact (runtime_mparameter b Hpb Hbv n S c s s' HCp (proj1 (bplain_parts env p S HCo)) (proj2 (bplain_parts env p S HCo)) Hnb Hvb' Hycb Hs Hd H Hr).
      - pose proof (HCt _ (or_intror ES)) as Hq. cbn [param_of] in Hq.
        assert (Ew: with_candidate env p c S = S) by (rewrite ES; exact (proj2 (candidate_reference env p c gm nn q Hq))).
        assert (Hvb': vars_in (bound_b b) S = true).
        { rewrite ES in Hvb |- *. cbn [vars_in] in Hvb |- *. rewrite andb_true_r in Hvb |- *.
          unfold param_eqb in Hvb. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hvb. exact Hvb. }
        rewrite Ew in H |- *. exact (runtime_mparameter b Hpb Hbv n S c s s' HCp (proj1 (bplain_parts env p S HCo)) (proj2 (bplain_parts env p S HCo)) Hnb Hvb' Hycb Hs Hd H Hr). }
    { destruct (Hinter cs eq_refl) as [Hif [Hcs Hunif]]. cbn [bound_components] in Hcomp, Hif |- *.
      assert (Hcomp': forall C, In C cs -> compfrag env C = true /\ bplain env p C = true /\ forall g, C = TypeVariable g -> param_of g <> p).
      { intros C HC. destruct (Hcomp C HC) as [_ [HCo HCt]]. split; [exact (Hif C HC)|]. split; [exact HCo|].
        intros g Eg. exact (HCt g (or_introl Eg)). }
      intros C HC.
      exact (rstatic_components n p cs c c s s' Hcomp' Hcs Hunif Hc Hbc Hqc
          (fun b' Hob' => conj Hc (conj Hbc (conj Hob' Hqc))) (fun _ E => E) Hs H b Hpb Hbv Hnb Hob Hvb Hd Hr C HC). }
    (* a nullable intersection: of the candidate without null, the components made nullable *)
    destruct (Hinter cs eq_refl) as [Hif [Hcs Hunif]]. cbn [bound_components] in Hcomp |- *.
    assert (Hcomp': forall C, In C cs -> compfrag env C = true /\ bplain env p C = true /\ forall g, C = TypeVariable g -> param_of g <> p).
    { intros C HC. destruct (Hcomp _ (in_map Nullable _ _ HC)) as [_ [HCo HCt]]. split; [exact (Hif C HC)|]. split; [exact (bplain_nullable env p C HCo)|].
      intros g Eg. apply (HCt g). right. rewrite Eg. reflexivity. }
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hshape]. rewrite length_map in Hlen.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases env wf p cs C Hif Hcs (fun g Hg => proj2 (proj2 (Hcomp' _ Hg)) g eq_refl) HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hshape _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
    change (with_candidate env p c (Nullable (Intersection cs))) with (rewrap_nullable (with_candidate env p c (Intersection cs))) in H.
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H. cbn [rewrap_nullable] in H.
    destruct n as [|n]; [discriminate H|].
    rewrite (nullable_target env n _ c s (proj1 Hc)) in H. rewrite <- (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    (* of a nullable bound, p is nullable *)
    assert (Hpn: is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env c = false)
        by (intros Hp; rewrite Hnl in Hp; discriminate Hp).
    intros C' HC'.
    apply in_map_iff in HC'. destruct HC' as [C [<- HC]].
    destruct (Hcomp' C HC) as [HCf [HCo HCt]].
    destruct (rstatic_components n p cs c (nullable_assignee env c) s s' Hcomp' Hcs Hunif Hc Hbc Hqc
        (fun b' Hob' => yfrag_nullable_assignee env wf declared caller (caller_nullable env declared ps) (caller_narrowed env wf declared ps)
            b' c (conj Hc (conj Hbc (conj Hob' Hqc)))) (fun Hp _ => Hpn Hp) Hs H b Hpb Hbv Hnb Hob Hvb Hd Hr C HC) as [f Hf].
    assert (HvC: vars_in (fun q => param_eqb q p || bound_b b q) C = true)
        by (cbn [vars_in] in Hvb; rewrite forallb_forall in Hvb; exact (Hvb C HC)).
    unfold rinst in Hf |- *.
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]]; subst C.
    - pose proof (compfrag_ifrag env _ HCf eq_refl) as HCi.
      destruct (Hone _ HCi HCo HCt HvC Hpn) as [_ [HcC _]]. destruct (instance_ground _ HcC) as [_ [_ HgZ]].
      change (with_candidate env p c (Nullable (RootResolved m cl args))) with (rewrap_nullable (with_candidate env p c (RootResolved m cl args))).
      rewrite (free_rewrap env b), rewrap_sigma.
      exact (runtime_nullable_variable c _ _ f (proj1 Hc) Hqc HgZ HgZ eq_refl Hf).
    - (* a type variable, narrowed or not, made nullable: the type it is bound to *)
      rewrite (proj2 (candidate_reference env p c gm nn q Hq)). rewrite (proj1 (candidate_reference env p c gm nn q Hq)) in Hf.
      change (instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn q []))))
          with (rewrap_nullable (instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])))).
      cbn [vars_in] in HvC. apply andb_true_iff in HvC. destruct HvC as [Hq' _].
      unfold param_eqb in Hq'. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hq'. cbn [orb] in Hq'. unfold bound_b in Hq'.
      destruct (lookup_binding b q) as [ab|] eqn:Ea; [|discriminate Hq'].
      destruct (Hpb q ab Ea) as [_ [o [y [-> _]]]].
      rewrite (free_variable_any env b Hpb gm nn q [] o y Ea) in Hf |- *. rewrite rewrap_sigma.
      destruct (Hbv q o y Ea) as [Hfy Hcy].
      assert (HgZ: ground env (instantiate env sigma (ref_apply env gm nn y)) = true).
      { rewrite (instance_ref_apply gm nn y Hfy Hcy). destruct (instance_ground y Hcy) as [_ [_ Hg]]. exact (ground_ref_apply gm nn _ Hg). }
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
          exact (below_trans env wf declared declared_wf terminates finite tame _ _ x Hbl Hfs Hx Hlo E1'). }
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
          intros Hnn Hnv b Hpb Hbv Hnb Hbd Ho Hv Hr.
          unfold st' in Hnn, Hnv, Ho, Hv |- *. cbn [lower_bound static_upper_bound] in Hnn, Hnv, Ho, Hv |- *.
          unfold gstatic_ok in Hok. rewrite Hnv in Hok. destruct Hok as [Hform _].
          exact (rstatic_whole n p _ c s s2 Hform Hfs Hbc Hqc Hs (Echk Hnv) b Hpb Hbv Hnb Ho Hv (dom_back b s _ Hk Hbd) (Hr2 b Hr)).
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
 * those of the callee. The type parameters of the class may be bounded by types mentioning them, as in
 * generic_member_call_with_bounded_variables_sound.
 *)
Theorem generic_receiver_with_bounded_variables_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (* the bounds of the type parameters of c: the declared ones, mentioning those of c *)
    (forall p S, In (p, S) cvars -> gstatic_bound env declared caller cvars p S) ->
    (forall p S, In (p, S) ovars -> gstatic_bound env declared caller (cvars ++ ovars) p S) ->
    (* the type parameters of c declared in order, before those of the function *)
    StronglySorted (fun p q => parameter_rank env p < parameter_rank env q) (map fst cvars) ->
    (forall p S q S', In (p, S) cvars -> In (q, S') ovars -> parameter_rank env p < parameter_rank env q) ->
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
    (forall P, In P Ps -> qfrag env P = true /\ (forall C, In C (intersected_components P) -> plain_owners C = true)
        /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true /\ caller A) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of env U (fst v)))) ovars ->
    (* the type arguments of the object within the bounds of the type parameters of c, instantiated *)
    (forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z ->
        exists o x, z = TypeArgument Model.invariant o x
            /\ if no_vars S then below env x S else forall C, In C (bound_components S) -> below env x (instantiate_free env b C)) ->
    (forall p S, In (p, S) ovars -> forall C, In C (bound_components S) ->
        exists f, unify env f (rinst b C) (instantiate env sigma (gfinal_of env U p)) (Ongoing []) = Some (Ongoing []))
    /\ forall P A, In (P, A) (combine Ps As) ->
        exists f, is_assignable_to env f (instantiate env sigma A) (instantiate env sigma (instantiate_free env b P)) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hcst Hst Hsort Hfn Hdis HfR HcR Hrec
        Hfo Hno Hcl Hobj Hzs Hxx HPs HPn HAs Hfold Hlow b Hbdef Hzb.
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    assert (Hvs: forall p S, In (p, S) (cvars ++ ovars) -> vars_in (static_vars env p) S = true).
    { intros p S Hin. apply in_app_or in Hin.
      destruct Hin as [Hin|Hin]; [destruct (Hcst p S Hin) as [_ [Hsv _]]|destruct (Hst p S Hin) as [_ [Hsv _]]];
          exact (vars_in_mono _ _ (fun q E => proj1 (proj1 (andb_true_iff _ _) E)) _ Hsv). }
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
    assert (Hfresh': forall p bound, In (p, bound) cvars ->
        lookup_state s0 p = Some (mkVariableState bound (initial_upper_bound bound) bottom_type false true)
        /\ vars_in (static_vars env p) bound = true)
        by (intros p bound Hin; split; [exact (Hfresh p bound Hin)|exact (Hvs p bound (in_or_app _ _ _ (or_introl Hin)))]).
    assert (Hrk0: ranked_states env s0).
    { intros q st Hq. unfold s0 in Hq. destruct (lookup_for_inference_in _ _ q st Hq) as [bound Hin].
      rewrite (lookup_for_inference _ _ q bound Hnd' Hin) in Hq. injection Hq as <-.
      cbn [upper_bound lower_bound static_upper_bound]. unfold initial_upper_bound.
      split; [destruct (no_vars bound) eqn:E; [exact E|reflexivity]|]. split; [reflexivity|exact (Hvs q bound Hin)]. }
    assert (Hlow0: forall q st, lookup_state s0 q = Some st -> is_exact st = false -> forall p bound, In (p, bound) cvars ->
        parameter_rank env q < parameter_rank env p -> In q (map fst cvars)).
    { intros q st Hq _ p bound Hin Hr. unfold s0 in Hq. destruct (lookup_for_inference_in _ _ q st Hq) as [bq Hinq].
      apply in_app_or in Hinq. destruct Hinq as [Hinq|Hinq]; [exact (in_map fst _ _ Hinq)|].
      pose proof (Hfn p bound q bq Hin Hinq). lia. }
    destruct (capture_arguments_checked env wf intersect_no_vars supertype_no_vars (argument_gfrag env) argument_gfrag_shape
        n cvars ys' s0 u Hndc Hl Hsort (fun y Hy => proj1 (Hys y Hy)) Hfresh' Hrk0 Hlow0 Hrec) as [Hcap Hoth].
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
          exact (Hvs p bound (in_or_app _ _ _ (or_introl (nth_error_In _ _ Hi)))).
        + exact (ginitial_ok env wf declared declared_wf terminates finite tame caller caller_top' caller_bottom'
              vars p bound u (Hst p bound Hin)).
      - intros p st Hp He'. destruct (Hu p st Hp) as [[i [bound [y [Hi [Hy ->]]]]]|[bound [Hin ->]]]; [discriminate He'|].
        intros E. cbn [lower_bound] in E. change (class_eqb nothing nothing = false) in E. rewrite class_eqb_refl in E. discriminate E. }
    (* the states the fold ends with *)
    assert (Hstep0: forall P A, In (P, A) (combine Ps As) -> forall s s', gw3 s ->
        unify env nf P A (Ongoing s) = Some (Ongoing s') ->
        gw3 s' /\ (forall b', gsatisfies env declared b' s' -> gsatisfies env declared b' s)).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP [HoP _]]. destruct (HAs A HA) as [HfA [HbA HqA]].
      destruct (mqparameter env wf declared declared_wf terminates finite tame caller Qa
          (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
          (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
          (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) [] plain_nil (bf_nil env declared)
          gw3 gw3_capturable nf (fun k _ => rleaf_all k [])
          P A s s' HfP HoP (HPn P HP) (nonnull_nil env) (conj HfA (conj HbA (conj (owners_free_nil env A) HqA))) Hs E)
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
      destruct (gfinal_value_fits env wf declared declared_wf terminates finite tame caller U p st ref HgU Hl' He') as [Hf Hfit].
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
    { destruct (below_refl env wf declared declared_wf terminates finite tame D (ground_of_fragment env declared D HgD)) as [[|f] Ef];
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
    (* the values of non-null bounds aren't null: the type arguments of the object, within the bounds,
       by the ranks of the type parameters of c, whose bounds mention only those *)
    assert (Hnvc: forall q o x, existsb (param_eqb q) (map fst cvars) = true -> lookup_binding b q = Some (TypeArgument Model.invariant o x) ->
        is_nullable env (Generic (mkGenericRef None false q [])) = false -> is_nullable env x = false).
    { apply (values_not_nullable_among env wf declared declared_wf (fun q => existsb (param_eqb q) (map fst cvars)) b Hpb
          (fun q o x Eq => proj1 (Hbv q o x Eq))).
      intros q o x HQ Eq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin _]]].
      2:{ exfalso. apply existsb_exists in HQ. destruct HQ as [q' [Hq' Eq']]. apply param_eqb_eq in Eq'. subst q'.
          exact (nodup_app_disjoint _ _ q Hnd Hq' (in_map fst _ _ Hin)). }
      destruct (Hzb i q S z Hi Hz) as [o' [x' [Ez' Hw]]]. rewrite Ez' in Ez. injection Ez as <- <-.
      destruct (Hcst q S (nth_error_In _ _ Hi)) as [ES [Hsv [Hcl' Hvar]]]. exists S. split; [exact ES|].
      destruct (no_vars S) eqn:Ens.
      - left. split; [exact (proj1 (proj1 (Hcl' eq_refl)))|exact Hw].
      - right; right. intros C HC. destruct (Hvar eq_refl) as [Hcomp _]. destruct (Hcomp C HC) as [HCp _].
        split; [exact HCp|]. split; [|exact (Hw C HC)].
        refine (vars_in_mono _ _ _ C (vars_in_bound_component _ S C Hsv HC)).
        intros q' E. apply andb_true_iff in E. destruct E as [_ E]. rewrite E, andb_true_r.
        apply Hdomb. unfold vars. rewrite map_app. apply in_or_app. left. apply existsb_exists in E. destruct E as [q'' [Hq'' E]].
        apply param_eqb_eq in E. subst q''. exact Hq''. }
    (* and the final values *)
    assert (Hnv: nonnull_values env b).
    { intros q o x Eq Hnq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - refine (Hnvc q o x _ Eq Hnq). apply existsb_exists. exists q.
        split; [exact (in_map fst _ _ (nth_error_In _ _ Hi))|apply param_eqb_refl].
      - injection Ea as _ ->.
        destruct (Hfin q S Hin) as [st [HlU [He' [Hs [Ef _]]]]]. destruct (Hst q S Hin) as [ES [_ [Hcl' _]]]. subst S.
        rewrite Ef. exact (gfinal_not_nullable env wf declared declared_wf terminates finite tame caller U q st HgU HlU He' ES
            (fun E => proj1 (Hcl' E)) (fun E => Hlow q _ st Hin E HlU) Hnq). }
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
        destruct (bound_component_of env wf declared declared_wf terminates finite tame caller (caller_component env declared ps)
            (caller_nullable_component env declared ps)
            S C HfS HqS HC) as [HfC [HqC HSC]].
        unfold rinst.
        rewrite (free_unmentioned env b Hpb C (proj1 HfC) (unmentioned env b C (proj1 HfC) (Hown' C HqC))).
        exact (subst_below _ C Hq HqC (below_trans env wf declared declared_wf terminates finite tame _ S C Hf HfS HfC
            (Hok _ Hf Hup) HSC)).
      + (* with them: the lower bound, checked against it at run time *)
        destruct Hok as [[Hcomp _] _]. destruct (Hcomp C HC) as [HCp [HCo HCt]].
        pose proof (Hlow p S st Hin Ens HlU) as Hnn.
        assert (Exl: gfinal_of env U p = lower_bound st) by (rewrite Ef; unfold Constraints.final_value; rewrite Hnn; reflexivity).
        assert (Hvb: vars_in (fun q => param_eqb q p || bound_b b q) S = true).
        { apply (vars_in_mono (bound_b b)); [intros q E; rewrite E; apply orb_true_r|].
          apply Hbound. apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ Hsv). }
        pose proof (HcU p st HlU He' Hnn) as Hchk. unfold rstatic_checked in Hchk. rewrite Hs in Hchk.
        pose proof (Hchk Ens b Hpb Hbv Hnv HdU (Hown' _ Hql) Hvb Hrsat C HC) as [f Hc'].
        exists f. rewrite Exl. unfold rinst in Hc' |- *. destruct (ifrag env C) eqn:HCi.
        *
          rewrite (free_candidate env b p (lower_bound st) C Hpb (proj1 Hfl) (unmentioned env b _ (proj1 Hfl) (Hown' _ Hql))
              (ref_apply_free env wf declared declared_wf b _ Hpb Hfl (Hown' _ Hql)) (ifrag_plain_variables env wf p C HCi HCo)) in Hc'.
          rewrite (free_ext env _ b (with_value_same b p (lower_bound st) ltac:(rewrite (HlbO p S Hin), Exl; reflexivity)) C) in Hc'.
          exact Hc'.
        * (* a type variable of a mutability given to it, narrowed or made nullable, other than p *)
          destruct (pfrag_cases env C HCp) as [H|[[gm [nn [q [EC _]]]]|[gm [nn [q [EC _]]]]]]; [rewrite H in HCi; discriminate HCi| |];
              subst C; [rewrite (proj1 (candidate_reference env p _ gm nn q (HCt _ (or_introl eq_refl)))) in Hc'
                       |rewrite (proj2 (candidate_reference env p _ gm nn q (HCt _ (or_intror eq_refl)))) in Hc']; exact Hc'.
    - (* each argument, in turn *)
      intros P A HPA.
      destruct (rfold2 b (fun x inner => let '(P', A') := x in unify env nf P' A' inner)
          (fun x => let '(P', A') := x in exists f,
              unify env f (instantiate env sigma (instantiate_free env b P')) (instantiate env sigma A') (Ongoing []) = Some (Ongoing []))
          (combine Ps As) u U) as [_ [_ [_ [_ Hall]]]].
      + intros [P' A']. apply unify_keeps_failure.
      + intros [P' A'] Hin s1 s1' Hs1 Hd1 E. apply in_combine_l in Hin as HP'. apply in_combine_r in Hin as HA'.
        destruct (HPs P' HP') as [HfP [HoP HvP]]. destruct (HAs A' HA') as [HfA [HbA HqA]].
        destruct (mqparameter env wf declared declared_wf terminates finite tame caller Qa
            (caller_argument_nested env declared ps) caller_top' caller_bottom' (caller_any env wf declared ps) (caller_root env declared ps)
            (caller_nullable env declared ps) (caller_bound env wf declared ps) (caller_narrowed env wf declared ps)
            (caller_component env declared ps) (caller_supertype_arguments env wf declared ps) [] plain_nil (bf_nil env declared)
            gw (gwf2_capturable env declared caller) nf (fun k _ => gleaf k [])
            P' A' s1 s1' HfP HoP (HPn P' HP') (nonnull_nil env) (conj HfA (conj HbA (conj (owners_free_nil env A') HqA)))
            Hs1 E) as [Hs1' [Hm1 _]].
        split; [exact Hs1'|]. split; [exact Hm1|]. split; [exact (unify_keeps_exact env nf P' A' s1 s1' E)|].
        intros Hr. pose proof (Hbound P' HvP) as HvP'.
        exact (runtime_mqparameter b Hpb Hbv nf P' A' s1 s1' HfP HoP (HPn P' HP') Hnv HvP' (conj HfA (conj HbA (conj (Hown' A' HqA) HqA)))
            Hs1 Hd1 E Hr).
      + exact (proj1 Hwfu).
      + exact Hdu.
      + exact Hfold.
      + destruct (Hall Hrsat (P, A) HPA) as [f Ef]. exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.

End Bounded.

End Receivers.

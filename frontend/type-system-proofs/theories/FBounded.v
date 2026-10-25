From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import WithinBounds.
From EmergeTypeSystem Require Import MemberCalls.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Inference with type variables bounded by type variables                                         *)
(*                                                                                                *)
(* The declared bound of a type parameter may mention the other type parameters of the function,  *)
(* `fn f<A, B : List<A>>`, and the parameter itself, `fn max<T : Comparable<T>>` (an F-bound).    *)
(* Inference keeps such a bound as the static upper bound of the variable, and checks each lower  *)
(* bound against it with the lower bound in place of the variable itself (plus_static_check),    *)
(* which constrains the other variables. Whatever unify accepts, it accepts with the variables    *)
(* replaced by their final values; and the final values are within the declared bounds,           *)
(* instantiated with them (invocation_with_bounded_variables_sound). The same holds for member    *)
(* functions, whose bounds may mention the type parameters of the class, captured by the receiver *)
(* (member_call_with_bounded_variables_sound).                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Section FBounded.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

(* Bindings to type arguments that aren't loose, whose types aren't type arguments *)
Definition plain_bindings (b: Bindings): Prop :=
    forall q a, lookup_binding b q = Some a -> is_loose a = false
        /\ exists o y, a = TypeArgument invariant o y /\ is_type_argument y = false
            /\ forall z, y = Nullable z -> is_type_argument z = false.

Lemma plain_not_loose: forall b, plain_bindings b -> forall q a, lookup_binding b q = Some a -> is_loose a = false.
Proof. intros b Hb q a E. exact (proj1 (Hb q a E)). Qed.

(* A type of the parameters, its type variables bound, as a type parameter instantiated, isn't a type
   argument *)
Lemma instantiate_ifrag_shape: forall b t, plain_bindings b -> ifrag env t = true -> bound_vars b t = true ->
    is_type_argument (instantiate env b (to_generic t)) = false
    /\ forall z, instantiate env b (to_generic t) = Nullable z -> is_type_argument z = false.
Proof.
    intros b t Hb Ht Hv. destruct (ifrag_cases env wf t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[q [-> _]]]]].
    - cbn [to_generic instantiate]. split; [reflexivity|]. intros z E. discriminate E.
    - cbn [to_generic instantiate map bottom_type]. split; [reflexivity|]. intros z E. discriminate E.
    - cbn [to_generic instantiate]. cbn [rewrap_nullable]. split; [reflexivity|]. intros z E. injection E as <-. reflexivity.
    - simpl in Hv. cbn [to_generic instantiate]. destruct (lookup_binding b q) as [a|] eqn:E; [|discriminate Hv].
      destruct (Hb q a E) as [Hl [o [y [-> [Hy Hz]]]]]. unfold final_argument. rewrite Hl.
      destruct (nests_argument y) eqn:En.
      + destruct y as [| [] | | | | |]; try discriminate En; try discriminate Hy. specialize (Hz _ eq_refl). discriminate Hz.
      + cbn [orb]. split; [exact Hy|exact Hz].
Qed.

Lemma closed_instantiate: forall b x, afrag env x = true -> closed x = true -> instantiate env b x = x.
Proof.
    intros b x Ha Hc. destruct (afrag_parts env x Ha) as [Hf Hn].
    pose proof (inst_nested_closed env wf b 0 [] x (class_sfrag env x Hf Hn) Hc) as E.
    destruct (fragment_cases env x Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact E.
Qed.

Lemma closed_plain_owners: forall t, closed t = true -> plain_owners t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try discriminate H; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite Ho, (IH n Hn). reflexivity.
Qed.

Lemma afrag_rewrap: forall X, afrag env X = true -> afrag env (rewrap_nullable X) = true.
Proof.
    intros X H. destruct (afrag_parts env X H) as [Hf _].
    destruct (fragment_cases env X Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact H.
Qed.

Lemma closed_rewrap: forall X, closed (rewrap_nullable X) = closed X.
Proof. intros [| | | | | |]; reflexivity. Qed.

Lemma afrag_shape: forall X, afrag env X = true -> is_type_argument X = false /\ forall z, X = Nullable z -> is_type_argument z = false.
Proof.
    intros X H. destruct (afrag_parts env X H) as [Hf _].
    destruct (fragment_cases env X Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity.
Qed.

(* A reference to a type variable, in a type argument, with a candidate for a variable: the instance of
   the candidate by the reference where it is to that variable, as it is otherwise *)
Lemma candidate_nested: forall p x gm nn q n, afrag env x = true -> closed x = true ->
    (n = TypeVariable (mkGenericRef gm nn q []) \/ n = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    (q <> p /\ instantiate env [(p, TypeArgument invariant ref x)] n = n)
    \/ (q = p /\ afrag env (instantiate env [(p, TypeArgument invariant ref x)] n) = true
        /\ closed (instantiate env [(p, TypeArgument invariant ref x)] n) = true
        /\ (n = TypeVariable (mkGenericRef gm nn q []) -> instantiate env [(p, TypeArgument invariant ref x)] n = ref_apply env gm nn x)
        /\ (n = Nullable (TypeVariable (mkGenericRef gm nn q [])) ->
            instantiate env [(p, TypeArgument invariant ref x)] n = rewrap_nullable (ref_apply env gm nn x))).
Proof.
    intros p x gm nn q n Hx Hcx En. destruct (ref_apply_afrag env wf gm nn x Hx) as [Hr Hrc]. rewrite Hcx in Hrc.
    destruct (param_eqb q p) eqn:Epq.
    - right. apply Nat.eqb_eq in Epq. subst q.
      assert (El: lookup_binding [(p, TypeArgument invariant ref x)] p = Some (TypeArgument invariant ref x))
          by (simpl; rewrite param_eqb_refl; reflexivity).
      assert (Ei: instantiate env [(p, TypeArgument invariant ref x)] (TypeVariable (mkGenericRef gm nn p [])) = ref_apply env gm nn x)
          by (rewrite (instantiate_reference env _ gm nn p [] _ El), (candidate_final env x Hx); reflexivity).
      split; [reflexivity|]. destruct En as [-> | ->].
      + rewrite Ei. split; [exact Hr|]. split; [exact Hrc|]. split; [reflexivity|intros E; discriminate E].
      + rewrite (instantiate_nullable_any env), Ei. split; [exact (afrag_rewrap _ Hr)|]. rewrite closed_rewrap.
        split; [exact Hrc|]. split; [intros E; discriminate E|reflexivity].
    - left. split; [intros E; subst q; rewrite param_eqb_refl in Epq; discriminate Epq|].
      assert (El: lookup_binding [(p, TypeArgument invariant ref x)] q = None) by (simpl; rewrite Epq; reflexivity).
      destruct En as [-> | ->]; [|rewrite (instantiate_nullable_any env)];
          rewrite (instantiate_unbound_variable env _ (mkGenericRef gm nn q []) El); reflexivity.
Qed.

(* A type of the parameters made the type of a type argument: its references to type variables plain *)
Lemma args_plain_wrap: forall v o y, ifrag env y = true -> args_plain y = true -> args_plain (TypeArgument v o y) = true.
Proof.
    intros v o y Hy H. destruct (ifrag_cases env wf y Hy) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[q [-> _]]]]];
        first [exact H|reflexivity].
Qed.

Lemma args_plain_candidate: forall p x, afrag env x = true -> closed x = true ->
    forall S, ifrag env S = true -> args_plain S = true -> args_plain (with_candidate env p x S) = true.
Proof.
    intros p x Hx Hcx.
    assert (Hcb: forall q a, lookup_binding [(p, TypeArgument invariant ref x)] q = Some a -> is_loose a = false).
    { intros q a E. simpl in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hshape: forall t, ifrag env t = true -> is_type_argument t = false /\ forall z, t = Nullable z -> is_type_argument z = false).
    { intros t Ht. destruct (ifrag_cases env wf t Ht) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity. }
    intros S. unfold with_candidate. remember (vsize S) as k eqn:Hk. revert S Hk.
    induction k as [k IH] using lt_wf_ind. intros S -> HS Hpl.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> [Hn [Hl Hargs]]]]]]|[->|[[m [c' [args [-> Hr]]]]|[q [-> _]]]]].
    - cbn [instantiate]. change (forallb args_plain (map (instantiate env [(p, TypeArgument invariant ref x)]) args) = true).
      apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (Hargs a Ha) as Ea.
      change (forallb args_plain args = true) in Hpl. rewrite forallb_forall in Hpl. pose proof (Hpl _ Ha) as Hpa.
      destruct a as [| | | |v o n| |]; try discriminate Ea. change (nfrag env n = true) in Ea.
      destruct (nfrag_cases env n Ea) as [Ea'|[gm [nn [q [Eq _]]]]].
      + pose proof (with_candidate_ifrag env wf p x Hx Hcx n Ea') as Hwn. unfold with_candidate in Hwn. destruct (Hshape _ Hwn) as [Ht1 Hz1].
        rewrite (instantiate_unloose_argument env _ v o n Hcb Ht1 Hz1). apply (args_plain_wrap _ _ _ Hwn).
        apply (IH (vsize n)); [|reflexivity|exact Ea'|exact (args_plain_argument v o n Hpa)].
        pose proof (vsize_below m c' args _ Ha) as Hv. simpl in Hv |- *. lia.
      + destruct (candidate_nested p x gm nn q n Hx Hcx Eq) as [[_ Hsame]|[_ [HN [HcN _]]]].
        * assert (Hsh: is_type_argument (instantiate env [(p, TypeArgument invariant ref x)] n) = false
              /\ forall z, instantiate env [(p, TypeArgument invariant ref x)] n = Nullable z -> is_type_argument z = false)
              by (rewrite Hsame; destruct Eq as [-> | ->]; split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity).
          rewrite (instantiate_unloose_argument env _ v o n Hcb (proj1 Hsh) (proj2 Hsh)), Hsame. exact Hpa.
        * destruct (afrag_shape _ HN) as [Ht Hz]. rewrite (instantiate_unloose_argument env _ v o n Hcb Ht Hz).
          pose proof (no_vars_args_plain _ (in_fragment_no_vars env _ (proj1 (afrag_parts env _ HN)))) as Hp.
          destruct (afrag_parts env _ HN) as [HfN _].
          destruct (fragment_cases env _ HfN) as [[m0 [c0 [a0 E]]]|[m0 [c0 [a0 [E _]]]]]; rewrite E in Hp |- *; exact Hp.
    - reflexivity.
    - change (args_plain (rewrap_nullable (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args))) = true).
      cbn [instantiate rewrap_nullable args_plain].
      change (args_plain (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args)) = true).
      apply (IH (vsize (RootResolved m c' args))); [simpl; lia|reflexivity|exact Hr|exact Hpl].
    - cbn [instantiate lookup_binding]. destruct (param_eqb q p); [|reflexivity]. rewrite (candidate_final env x Hx).
      exact (no_vars_args_plain _ (in_fragment_no_vars env _ (proj1 (afrag_parts env _ Hx)))).
Qed.

(* The type variables bound in b *)
Definition bound_in_b (b: Bindings) (q: TypeParameterId): bool := match lookup_binding b q with Some _ => true | None => false end.

Lemma vars_in_bound_vars: forall b t, vars_in (bound_in_b b) t = true -> bound_vars b t = true.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] H; simpl in H |- *; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - exact (IH n H).
    - apply andb_true_iff in H. unfold bound_in_b in H. destruct (lookup_binding b q); [reflexivity|destruct H as [E _]; discriminate E].
Qed.

Lemma bound_vars_in: forall b t, no_generics t = true -> bound_vars b t = true -> vars_in (bound_in_b b) t = true.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|[[gm|] [|] q [|w ws]]|cs] Hn H; simpl in Hn, H |- *; try discriminate Hn; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Hn, H |- *. apply andb_true_iff in Hn, H.
      rewrite (IH a (proj1 Hn) (proj1 H)), (IHa (proj2 Hn) (proj2 H)). reflexivity.
    - apply andb_true_iff in Hn. exact (IH n (proj2 Hn) H).
    - apply orb_true_iff in Hn. destruct Hn as [Hn|Hn]; [exact (IH n Hn H)|]. clear IH.
      destruct n as [|[| | | | |[gm nn q []]|]| | | |[gm nn q []]|]; try discriminate Hn; simpl in H |- *;
          unfold bound_in_b; destruct (lookup_binding b q); first [reflexivity|discriminate H].
    - unfold bound_in_b. destruct (lookup_binding b q); [reflexivity|discriminate H].
Qed.

Lemma bound_vars_candidate: forall b p x S, no_generics S = true -> bound_vars b S = true -> no_vars x = true ->
    bound_vars b (with_candidate env p x S) = true.
Proof.
    intros b p x S Hn Hv Hx. apply vars_in_bound_vars.
    apply (vars_in_mono (fun q => bound_in_b b q && negb (param_eqb q p))); [intros q E; apply andb_true_iff in E; exact (proj1 E)|].
    exact (candidate_vars env wf _ p x S (bound_vars_in b S Hn Hv) Hx).
Qed.

(* The static upper bound of a variable with a candidate for the variable, instantiated with bindings
   that bind the variable to that candidate, is the declared bound instantiated *)
Lemma candidate_instantiate_nested: forall b p o x, plain_bindings b -> lookup_binding b p = Some (TypeArgument invariant o x) ->
    afrag env x = true -> closed x = true ->
    forall v o' gm nn q n, (n = TypeVariable (mkGenericRef gm nn q []) \/ n = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    negb (is_parameter_ownership o') = true ->
    instantiate env b (to_generic (instantiate env [(p, TypeArgument invariant ref x)] (TypeArgument v o' n)))
    = instantiate env b (to_generic (TypeArgument v o' n)).
Proof.
    intros b p o x Hb Ep Hx Hcx v o' gm nn q n En Hop.
    assert (Hcb: forall q' a, lookup_binding [(p, TypeArgument invariant ref x)] q' = Some a -> is_loose a = false).
    { intros q' a E. simpl in E. destruct (param_eqb q' p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Ho1: forall bb, instantiate_ownership bb o' = o') by (intros bb; destruct o'; try discriminate Hop; reflexivity).
    destruct (candidate_nested p x gm nn q n Hx Hcx En) as [[_ Hsame]|[-> [HN [HcN [E1 E2]]]]].
    - (* to another variable: as it is *)
      assert (Hsh: is_type_argument (instantiate env [(p, TypeArgument invariant ref x)] n) = false
          /\ forall z, instantiate env [(p, TypeArgument invariant ref x)] n = Nullable z -> is_type_argument z = false)
          by (rewrite Hsame; destruct En as [-> | ->]; split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity).
      rewrite (instantiate_unloose_argument env _ v o' n Hcb (proj1 Hsh) (proj2 Hsh)), Ho1, Hsame. reflexivity.
    - (* to the variable: the instance of the candidate, by both *)
      assert (Hbn: instantiate env b (to_generic n) = instantiate env [(p, TypeArgument invariant ref x)] n).
      { assert (Hbx: instantiate env b (Generic (mkGenericRef gm nn p [])) = ref_apply env gm nn x).
        { cbn [instantiate]. rewrite Ep. unfold final_argument. rewrite (proj1 (Hb p _ Ep)).
          destruct (afrag_parts env x Hx) as [Hf _].
          destruct (fragment_cases env x Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; unfold ref_apply; destruct gm, nn; reflexivity. }
        destruct En as [En|En]; [rewrite (E1 En), En; exact Hbx|rewrite (E2 En), En].
        change (rewrap_nullable (instantiate env b (Generic (mkGenericRef gm nn p [])))
            = rewrap_nullable (ref_apply env gm nn x)). rewrite Hbx. reflexivity. }
      destruct (afrag_shape _ HN) as [Ht Hz].
      rewrite (instantiate_unloose_argument env _ v o' n Hcb Ht Hz), Ho1.
      remember (instantiate env [(p, TypeArgument invariant ref x)] n) as N eqn:EN.
      try rewrite <- EN in HN; try rewrite <- EN in HcN; try rewrite <- EN in Ht; try rewrite <- EN in Hz; try rewrite <- EN in Hbn.
      cbn [to_generic]. rewrite (to_generic_closed N HcN).
      assert (Hbs: is_type_argument (instantiate env b (to_generic n)) = false
          /\ forall z, instantiate env b (to_generic n) = Nullable z -> is_type_argument z = false) by (rewrite Hbn; exact (conj Ht Hz)).
      rewrite (instantiate_unloose_argument env b v o' _ (plain_not_loose b Hb) (proj1 Hbs) (proj2 Hbs)), Hbn.
      assert (Hbs': is_type_argument (instantiate env b N) = false /\ forall z, instantiate env b N = Nullable z -> is_type_argument z = false)
          by (rewrite (closed_instantiate b N HN HcN); exact (conj Ht Hz)).
      rewrite (instantiate_unloose_argument env b v o' N (plain_not_loose b Hb) (proj1 Hbs') (proj2 Hbs')), Ho1,
          (closed_instantiate b N HN HcN). reflexivity.
Qed.

Lemma candidate_instantiate: forall b p o x, plain_bindings b -> lookup_binding b p = Some (TypeArgument invariant o x) ->
    afrag env x = true -> closed x = true ->
    forall S, ifrag env S = true -> plain_owners S = true -> bound_vars b S = true ->
        instantiate env b (to_generic (with_candidate env p x S)) = instantiate env b (to_generic S).
Proof.
    intros b p o x Hb Ep Hx Hcx.
    assert (Hcb: forall q a, lookup_binding [(p, TypeArgument invariant ref x)] q = Some a -> is_loose a = false).
    { intros q a E. simpl in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hshape: forall t, ifrag env t = true -> is_type_argument t = false /\ forall z, t = Nullable z -> is_type_argument z = false).
    { intros t Ht. destruct (ifrag_cases env wf t Ht) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity. }
    intros S. unfold with_candidate. remember (vsize S) as k eqn:Hk. revert S Hk.
    induction k as [k IH] using lt_wf_ind. intros S -> HS Ho Hv.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> [Hn [Hl Hargs]]]]]]|[->|[[m [c' [args [-> Hr]]]]|[q [-> _]]]]].
    - cbn [instantiate to_generic]. rewrite !map_map. f_equal. apply map_ext_in. intros a Ha.
      pose proof (Hargs a Ha) as Ea. destruct a as [| | | |v o' n| |]; try discriminate Ea. change (nfrag env n = true) in Ea.
      change (forallb plain_owners args = true) in Ho. rewrite forallb_forall in Ho. pose proof (Ho _ Ha) as Hon.
      change (negb (is_parameter_ownership o') && plain_owners n = true) in Hon. apply andb_true_iff in Hon. destruct Hon as [Hop Hon].
      change (forallb (bound_vars b) args = true) in Hv. rewrite forallb_forall in Hv. pose proof (Hv _ Ha) as Hvn. simpl in Hvn.
      destruct (nfrag_cases env n Ea) as [Ea'|[gm [nn [q [Eq _]]]]];
          [clear Ea; rename Ea' into Ea|exact (candidate_instantiate_nested b p o x Hb Ep Hx Hcx v o' gm nn q n Eq Hop)].
      pose proof (with_candidate_ifrag env wf p x Hx Hcx n Ea) as Hwn. unfold with_candidate in Hwn.
      destruct (Hshape _ Hwn) as [Ht1 Hz1].
      rewrite (instantiate_unloose_argument env _ v o' n Hcb Ht1 Hz1).
      replace (instantiate_ownership [(p, TypeArgument invariant ref x)] o') with o' by (destruct o'; try discriminate Hop; reflexivity).
      cbn [to_generic].
      assert (Hvwn: bound_vars b (instantiate env [(p, TypeArgument invariant ref x)] n) = true).
      { apply (bound_vars_candidate b p x n (ifrag_no_generics env n Ea) Hvn).
        exact (in_fragment_no_vars env x (proj1 (afrag_parts env x Hx))). }
      destruct (instantiate_ifrag_shape b _ Hb Hwn Hvwn) as [Ht2 Hz2].
      destruct (instantiate_ifrag_shape b _ Hb Ea Hvn) as [Ht3 Hz3].
      rewrite (instantiate_unloose_argument env b v o' _ (plain_not_loose b Hb) Ht2 Hz2).
      rewrite (instantiate_unloose_argument env b v o' _ (plain_not_loose b Hb) Ht3 Hz3).
      f_equal. apply (IH (vsize n)); [|reflexivity|exact Ea|exact Hon|exact Hvn].
      pose proof (vsize_below m c' args _ Ha) as Hvs. simpl in Hvs |- *. lia.
    - reflexivity.
    - assert (E: instantiate env b (to_generic (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args)))
          = instantiate env b (to_generic (RootResolved m c' args))).
      { apply (IH (vsize (RootResolved m c' args))); [simpl; lia|reflexivity|exact Hr|exact Ho|exact Hv]. }
      change (rewrap_nullable (instantiate env b (to_generic (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args))))
          = rewrap_nullable (instantiate env b (to_generic (RootResolved m c' args)))).
      rewrite E. reflexivity.
    - cbn [instantiate lookup_binding]. destruct (param_eqb q p) eqn:Eq.
      + apply Nat.eqb_eq in Eq. subst q. rewrite (candidate_final env x Hx), (to_generic_closed x Hcx), (closed_instantiate b x Hx Hcx).
        cbn [to_generic instantiate]. rewrite Ep. unfold final_argument.
        rewrite (proj1 (Hb p _ Ep)). destruct (afrag_parts env x Hx) as [Hf _].
        destruct (fragment_cases env x Hf) as [[m [c' [args ->]]]|[m [c' [args [-> _]]]]]; reflexivity.
      + reflexivity.
Qed.

Lemma vars_in_and: forall (P1 P2: TypeParameterId -> bool) t, vars_in P1 t = true -> vars_in P2 t = true ->
    vars_in (fun q => P1 q && P2 q) t = true.
Proof.
    intros P1 P2. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] H1 H2; simpl in H1, H2 |- *; try reflexivity; try exact H1.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H1, H2 |- *. apply andb_true_iff in H1, H2.
      rewrite (IH a (proj1 H1) (proj1 H2)), (IHa (proj2 H1) (proj2 H2)). reflexivity.
    - exact (IH n H1 H2).
    - exact (IH n H1 H2).
    - apply andb_true_iff in H1, H2. rewrite (proj1 H1), (proj1 H2). exact (proj2 H1).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in H1, H2 |- *. apply andb_true_iff in H1, H2.
      rewrite (IH c (proj1 H1) (proj1 H2)), (IHc (proj2 H1) (proj2 H2)). reflexivity.
Qed.

(* The type parameters in the ownerships of type arguments are among P *)
Fixpoint owners_in (P: TypeParameterId -> bool) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (owners_in P) arguments
    | Nullable n => owners_in P n
    | TypeArgument _ o n => match o with parameter_ownership q => P q | _ => true end && owners_in P n
    | _ => true
    end.

Lemma plain_owners_in: forall P t, plain_owners t = true -> owners_in P t = true.
Proof.
    intros P. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite (IH n Hn). destruct o; try reflexivity. discriminate Ho.
Qed.

(* The references of a type of the parameters, as type parameters *)
Lemma refs_of_vars: forall (P: TypeParameterId -> bool) (R: GenericRef -> Prop) b t, no_generics t = true ->
    vars_in P t = true -> owners_in P t = true -> args_plain t = true ->
    (forall q, P q = true -> R (mkGenericRef None false q [])) ->
    (forall q, P q = true -> ownership_bound b (parameter_ownership q) = true) ->
    refs_in b R (to_generic t).
Proof.
    intros P R b. fix IH 1. intros [m c args|n|g|me msg|v o n|[[gm|] [|] q [|w ws]]|cs] Hn Hv Ho Hpl HR Hb;
        simpl in Hn, Hv, Ho |- *; try discriminate Hn; try exact I.
    - induction args as [|a args IHa]; [exact I|]. simpl in Hn, Hv, Ho, Hpl |- *. apply andb_true_iff in Hn, Hv, Ho, Hpl.
      exact (conj (IH a (proj1 Hn) (proj1 Hv) (proj1 Ho) (proj1 Hpl) HR Hb) (IHa (proj2 Hn) (proj2 Hv) (proj2 Ho) (proj2 Hpl))).
    - apply andb_true_iff in Hn. exact (IH n (proj2 Hn) Hv Ho Hpl HR Hb).
    - apply andb_true_iff in Ho. destruct Ho as [Ho1 Ho2]. split; [destruct o as [| | |q]; try reflexivity; exact (Hb q Ho1)|].
      apply orb_true_iff in Hn. destruct Hn as [Hn|Hn]; [exact (IH n Hn Hv Ho2 (args_plain_argument v o n Hpl) HR Hb)|]. clear IH.
      destruct n as [|[| | | | |[gm nn q []]|]| | | |[gm nn q []]|]; try discriminate Hn; simpl in Hv, Hpl |- *;
          rewrite andb_true_r in Hv; destruct gm, nn; try discriminate Hpl; exact (HR q Hv).
    - apply HR. rewrite andb_true_r in Hv. exact Hv.
Qed.

Lemma refs_of_vars_any: forall (P: TypeParameterId -> bool) (R: GenericRef -> Prop) b t, no_generics t = true ->
    vars_in P t = true -> owners_in P t = true ->
    (forall gm nn q, P q = true -> R (mkGenericRef gm nn q [])) ->
    (forall q, P q = true -> ownership_bound b (parameter_ownership q) = true) ->
    refs_in b R (to_generic t).
Proof.
    intros P R b. fix IH 1. intros [m c args|n|g|me msg|v o n|[[gm|] [|] q [|w ws]]|cs] Hn Hv Ho HR Hb;
        simpl in Hn, Hv, Ho |- *; try discriminate Hn; try exact I.
    - induction args as [|a args IHa]; [exact I|]. simpl in Hn, Hv, Ho |- *. apply andb_true_iff in Hn, Hv, Ho.
      exact (conj (IH a (proj1 Hn) (proj1 Hv) (proj1 Ho) HR Hb) (IHa (proj2 Hn) (proj2 Hv) (proj2 Ho))).
    - apply andb_true_iff in Hn. exact (IH n (proj2 Hn) Hv Ho HR Hb).
    - apply andb_true_iff in Ho. destruct Ho as [Ho1 Ho2]. split; [destruct o as [| | |q]; try reflexivity; exact (Hb q Ho1)|].
      apply orb_true_iff in Hn. destruct Hn as [Hn|Hn]; [exact (IH n Hn Hv Ho2 HR Hb)|]. clear IH.
      destruct n as [|[| | | | |[gm nn q []]|]| | | |[gm nn q []]|]; try discriminate Hn; simpl in Hv |- *;
          rewrite andb_true_r in Hv; exact (HR gm nn q Hv).
    - apply (HR None false). rewrite andb_true_r in Hv. exact Hv.
Qed.

(* A type of the parameters, as type parameters, instantiates as a type in a type argument does *)
Lemma inst_nested_plain: forall b t, plain_bindings b -> ifrag env t = true -> bound_vars b t = true ->
    inst_nested env b (to_generic t) = instantiate env b (to_generic t).
Proof.
    intros b t Hb Ht Hv. destruct (ifrag_cases env wf t Ht) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[q [-> _]]]]];
        try reflexivity.
    simpl in Hv. cbn [to_generic inst_nested instantiate param_of]. destruct (lookup_binding b q) as [a|] eqn:E; [|discriminate Hv].
    destruct (Hb q a E) as [Hl [o [y [-> [Hy Hz]]]]]. unfold inst_ref, inst_fit. cbn [given_mutability is_narrowed].
    unfold final_argument. rewrite Hl. destruct (nests_argument y) eqn:En; [|reflexivity].
    destruct y as [| [] | | | | |]; try discriminate En; try discriminate Hy. specialize (Hz _ eq_refl). discriminate Hz.
Qed.

(* A type of the parameters without type variables, nor ownerships of type parameters, is a class type *)
Lemma closed_of_ifrag: forall t, ifrag env t = true -> no_vars t = true -> plain_owners t = true -> closed t = true.
Proof.
    intros t. remember (vsize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht Hn Ho.
    destruct (ifrag_cases env wf t Ht) as [[m [c [args [-> [_ [_ Hargs]]]]]]|[->|[[m [c [args [-> Hr]]]]|[q [-> _]]]]].
    - change (forallb closed args = true). apply forallb_forall. intros a Ha. pose proof (Hargs a Ha) as Ea.
      change (forallb no_vars args = true) in Hn. rewrite forallb_forall in Hn.
      change (forallb plain_owners args = true) in Ho. rewrite forallb_forall in Ho.
      destruct a as [| | | |v o n| |]; try discriminate Ea. change (nfrag env n = true) in Ea. pose proof (Hn _ Ha) as Hna. pose proof (Ho _ Ha) as Hoa.
      simpl in Hna, Hoa |- *. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon]. rewrite Hop. cbn [andb].
      destruct (nfrag_cases env n Ea) as [Ea'|[gm [nn [q [[-> | ->] _]]]]]; [|discriminate Hna|discriminate Hna].
      apply (IH (vsize n)); [|reflexivity|exact Ea'|exact Hna|exact Hon]. pose proof (vsize_below m c args _ Ha) as Hv. simpl in Hv |- *. lia.
    - reflexivity.
    - change (closed (RootResolved m c args) = true). apply (IH (vsize (RootResolved m c args))); [simpl; lia|reflexivity|exact Hr|exact Hn|exact Ho].
    - discriminate Hn.
Qed.

(* A static upper bound with a candidate of no ownerships of type parameters has none *)
Lemma plain_owners_candidate: forall p x, afrag env x = true -> closed x = true ->
    forall S, ifrag env S = true -> plain_owners S = true -> plain_owners (with_candidate env p x S) = true.
Proof.
    intros p x Hx Hcx.
    assert (Hcb: forall q a, lookup_binding [(p, TypeArgument invariant ref x)] q = Some a -> is_loose a = false).
    { intros q a E. simpl in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hshape: forall t, ifrag env t = true -> is_type_argument t = false /\ forall z, t = Nullable z -> is_type_argument z = false).
    { intros t Ht. destruct (ifrag_cases env wf t Ht) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity. }
    assert (Hxo: plain_owners x = true).
    { clear -Hcx. revert Hcx. revert x. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try discriminate H; try reflexivity.
      - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
        rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
      - exact (IH n H).
      - apply andb_true_iff in H. destruct H as [Ho Hn]. rewrite Ho, (IH n Hn). reflexivity. }
    intros S. unfold with_candidate. remember (vsize S) as k eqn:Hk. revert S Hk.
    induction k as [k IH] using lt_wf_ind. intros S -> HS Ho.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> [Hn [Hl Hargs]]]]]]|[->|[[m [c' [args [-> Hr]]]]|[q [-> _]]]]].
    - cbn [instantiate]. change (forallb plain_owners (map (instantiate env [(p, TypeArgument invariant ref x)]) args) = true).
      apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. pose proof (Hargs a Ha) as Ea.
      change (forallb plain_owners args = true) in Ho. rewrite forallb_forall in Ho. pose proof (Ho _ Ha) as Hoa.
      destruct a as [| | | |v o n| |]; try discriminate Ea. change (nfrag env n = true) in Ea. simpl in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
      destruct (nfrag_cases env n Ea) as [Ea'|[gm [nn [q [Eq _]]]]].
      2:{ (* a reference: of the candidate, a class type, or as it is *)
          destruct (candidate_nested p x gm nn q n Hx Hcx Eq) as [[_ Hsame]|[_ [HN [HcN _]]]].
          - assert (Hsh: is_type_argument (instantiate env [(p, TypeArgument invariant ref x)] n) = false
                /\ forall z, instantiate env [(p, TypeArgument invariant ref x)] n = Nullable z -> is_type_argument z = false)
                by (rewrite Hsame; destruct Eq as [-> | ->]; split; try reflexivity; intros z E; try discriminate E; injection E as <-; reflexivity).
            rewrite (instantiate_unloose_argument env _ v o n Hcb (proj1 Hsh) (proj2 Hsh)), Hsame.
            replace (instantiate_ownership [(p, TypeArgument invariant ref x)] o) with o by (destruct o; try discriminate Hop; reflexivity).
            change (negb (is_parameter_ownership o) && plain_owners n = true). rewrite Hop, Hon. reflexivity.
          - destruct (afrag_shape _ HN) as [Ht Hz]. rewrite (instantiate_unloose_argument env _ v o n Hcb Ht Hz).
            replace (instantiate_ownership [(p, TypeArgument invariant ref x)] o) with o by (destruct o; try discriminate Hop; reflexivity).
            change (negb (is_parameter_ownership o) && plain_owners (instantiate env [(p, TypeArgument invariant ref x)] n) = true).
            rewrite Hop, (closed_plain_owners _ HcN). reflexivity. }
      clear Ea. rename Ea' into Ea.
      pose proof (with_candidate_ifrag env wf p x Hx Hcx n Ea) as Hwn. unfold with_candidate in Hwn. destruct (Hshape _ Hwn) as [Ht1 Hz1].
      rewrite (instantiate_unloose_argument env _ v o n Hcb Ht1 Hz1).
      replace (instantiate_ownership [(p, TypeArgument invariant ref x)] o) with o by (destruct o; try discriminate Hop; reflexivity).
      change (negb (is_parameter_ownership o) && plain_owners (instantiate env [(p, TypeArgument invariant ref x)] n) = true).
      rewrite Hop. apply (IH (vsize n)); [|reflexivity|exact Ea|exact Hon]. pose proof (vsize_below m c' args _ Ha) as Hv. simpl in Hv |- *. lia.
    - reflexivity.
    - change (plain_owners (rewrap_nullable (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args))) = true).
      cbn [instantiate rewrap_nullable plain_owners].
      change (plain_owners (instantiate env [(p, TypeArgument invariant ref x)] (RootResolved m c' args)) = true).
      apply (IH (vsize (RootResolved m c' args))); [simpl; lia|reflexivity|exact Hr|exact Ho].
    - cbn [instantiate lookup_binding]. destruct (param_eqb q p); [|reflexivity]. rewrite (candidate_final env x Hx). exact Hxo.
Qed.

(* Below the instance of each component of an intersection, a class type is below the instance of the
   intersection, its type parameters bound to class types *)
Lemma below_intersection_instance: forall b K cs x, bindings_in_fragment env b -> components_sfrag env cs = true ->
    bex env b (Intersection cs) = true ->
    (forall c, In c cs -> bound_in_top_h env b K [] (top_bound_in env b K []) c = true) ->
    in_fragment env x = true ->
    (forall c, In c cs -> exists f, unify env f (inst_nested env b c) x (Ongoing []) = Some (Ongoing [])) ->
    exists f, unify env f (inst_nested env b (Intersection cs)) x (Ongoing []) = Some (Ongoing []).
Proof.
    intros b K cs x Hbf Hcs Hbx Htop Hx Hall.
    destruct (components_sfrag_facts env cs Hcs) as [Hl Hc].
    assert (Hn: forall c, In c cs -> is_nullable env (inst_nested env b c) = false).
    { intros c Hin. destruct (Hc c Hin) as [Hsh Hs].
      apply (proj2 (proj2 (instance_facts_ex env wf b K [] Hbf _ c (le_n _) (sfrag_tfrag env c Hs) (bex_component env b cs c Hbx Hin) (Htop c Hin)))).
      apply (component_non_null env), Hsh. }
    destruct (intersection_instance_ex env wf b Hbf cs Hcs Hbx Hn) as [Heq [Hcc Hcomp]]. rewrite Heq.
    destruct (uniform_fuel_list cs (fun f c => unify env f (inst_nested env b c) x (Ongoing []) = Some (Ongoing []))) as [f Hf].
    { intros f f' c Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { exact Hall. }
    assert (Hne: cs <> []) by (intros ->; simpl in Hl; lia).
    assert (HnA: is_nullable env x = false).
    { destruct cs as [|c1 cs']; [exfalso; exact (Hne eq_refl)|].
      exact (accepted_non_null env _ _ _ _ _ (proj1 (Hcomp c1 (or_introl eq_refl))) Hx (Hn c1 (or_introl eq_refl)) (Hf c1 (or_introl eq_refl))). }
    exists (S f). apply (inter_takes env); [exact Hcc|exact Hx|exact HnA|].
    intros y Hy. apply in_map_iff in Hy. destruct Hy as [y' [<- Hy']]. apply in_map_iff in Hy'. destruct Hy' as [c [<- Hin]].
    apply (accepts_with_mutability env); [exact (proj1 (Hcomp c Hin))|exact Hx| |exact (Hf c Hin)].
    apply Ops.fold_intersect_greatest; [apply Ops.mutability_subtype_of_readonly|].
    intros m Hm. apply in_map_iff in Hm. destruct Hm as [y [<- Hy]]. apply in_map_iff in Hy. destruct Hy as [c' [<- Hin']].
    exact (accepted_mutability_classes env _ _ _ _ _ (proj1 (Hcomp c' Hin')) Hx (Hf c' Hin')).
Qed.

(* The type parameters of the references of Rv, and those in the declared bounds of their parameters,
   have bindings *)
Lemma bex_of_refs: forall b (Rv: GenericRef -> Prop),
    (forall g, Rv g -> has_binding env b g = true /\ variables_of g = [] /\ refs_in b Rv (parameter_bound env (param_of g))) ->
    forall t, refs_in b Rv t -> bex env b t = true.
Proof.
    intros b Rv HRv. pose proof (wf_bounds_deep_ranked env wf) as deep.
    assert (Hlift: forall p k U, (forall q, q = p \/ parameter_rank env q < k -> (exists g, Rv g /\ param_of g = q) -> U q = true) ->
        forall t, deep_ranked env p k t = true -> refs_in b Rv t -> bex_h env b U t = true).
    { intros p k U HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hr Hb; simpl in Hr, Hb |- *; try reflexivity.
      - induction args as [|a args IHa]; [reflexivity|]. simpl in Hr, Hb |- *. apply andb_true_iff in Hr. destruct Hb as [Ha Has].
        rewrite (IH a (proj1 Hr) Ha), (IHa (proj2 Hr) Has). reflexivity.
      - exact (IH n Hr Hb).
      - destruct (HRv g Hb) as [Hh [Hv _]]. rewrite Hh. unfold no_type_variables. rewrite Hv. cbn [andb].
        exact (HU _ (deep_ranked_param env p k g Hr) (ex_intro _ g (conj Hb eq_refl))).
      - destruct Hb as [Ho Hn]. rewrite Ho. exact (IH n Hr Hn).
      - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hr, Hb |- *. apply andb_true_iff in Hr. destruct Hb as [Hc Hcs].
        rewrite (IH c (proj1 Hr) Hc), (IHc (proj2 Hr) Hcs). reflexivity. }
    assert (Hparam: forall q, (exists g, Rv g /\ param_of g = q) -> param_bex env b q = true).
    { intros q. remember (parameter_rank env q) as r eqn:Er. revert q Er. induction r as [r IH] using lt_wf_ind. intros q -> [g [Hg Eq]].
      unfold param_bex. rewrite (through_param_eq env (bex_h env b) true deep (bex_h_agree env b) q).
      apply (Hlift q (parameter_rank env q)); [|apply deep|].
      - intros q' [->|Hq'] Hex; [unfold param_eqb; rewrite Nat.eqb_refl; reflexivity|].
        destruct (param_eqb q' q); [reflexivity|]. exact (IH _ Hq' q' eq_refl Hex).
      - destruct (HRv g Hg) as [_ [_ Hb]]. rewrite Eq in Hb. exact Hb. }
    intros t Ht. destruct (deep_ranked_exists env 0 t) as [k Hk]. rewrite (bex_top env b).
    apply (Hlift 0 k); [|exact Hk|exact Ht]. intros q _ Hex. exact (Hparam q Hex).
Qed.

(* A static upper bound: an intersection, nullable or not, or of no components but itself *)
Lemma static_shape: forall S,
    (intersected_components S = [S] /\ inter_of S = None)
    \/ (exists cs, S = Intersection cs /\ intersected_components S = cs)
    \/ (exists cs, S = Nullable (Intersection cs) /\ intersected_components S = map Nullable cs).
Proof.
    intros [m c args|[| | | | | |cs]|g|me msg|v o n|g|cs];
        first [left; split; reflexivity|right; left; exists cs; split; reflexivity|right; right; exists cs; split; reflexivity].
Qed.

(* The components of a bound: those of an intersection, nullable or not, or the bound itself *)
Definition components_of (S: EType): list EType :=
    match S with Intersection cs | Nullable (Intersection cs) => cs | _ => [S] end.

Lemma components_of_none: forall S, inter_of S = None -> components_of S = [S].
Proof. intros [| [| | | | | |?] | | | | |?] E; try reflexivity; discriminate E. Qed.

Lemma args_plain_components: forall S, args_plain S = true -> forall C, In C (components_of S) -> args_plain C = true.
Proof.
    intros S H C HC. destruct (static_shape S) as [[E Ei]|[[cs [-> _]]|[cs [-> _]]]].
    - rewrite (components_of_none S Ei) in HC. destruct HC as [<-|[]]. exact H.
    - cbn [args_plain components_of] in H, HC. rewrite forallb_forall in H. exact (H C HC).
    - cbn [args_plain components_of] in H, HC. rewrite forallb_forall in H. exact (H C HC).
Qed.

Lemma args_plain_intersected: forall S, args_plain S = true -> forall C, In C (intersected_components S) -> args_plain C = true.
Proof.
    intros S H C HC. destruct (static_shape S) as [[E Ei]|[[cs [-> E]]|[cs [-> E]]]]; rewrite E in HC.
    - destruct HC as [<-|[]]. exact H.
    - cbn [args_plain] in H. rewrite forallb_forall in H. exact (H C HC).
    - cbn [args_plain] in H. rewrite forallb_forall in H. apply in_map_iff in HC. destruct HC as [c [<- Hc]]. exact (H c Hc).
Qed.

Lemma args_plain_not_in_fragment: forall S, args_plain S = false -> in_fragment env S = false.
Proof.
    intros S E. destruct (in_fragment env S) eqn:Ef; [|reflexivity].
    rewrite (no_vars_args_plain S (in_fragment_no_vars env S Ef)) in E. discriminate E.
Qed.

Lemma components_of_owners: forall S, (forall C, In C (intersected_components S) -> plain_owners C = true) ->
    forall C, In C (components_of S) -> plain_owners C = true.
Proof.
    intros S H C HC. destruct (static_shape S) as [[E Ei]|[[cs [-> _]]|[cs [-> _]]]].
    - rewrite (components_of_none S Ei) in HC. rewrite E in H. exact (H C HC).
    - exact (H C HC).
    - exact (H (Nullable C) (in_map Nullable _ _ HC)).
Qed.

(* The references of a static upper bound, as type parameters *)
Lemma refs_of_static: forall (P: TypeParameterId -> bool) (R: GenericRef -> Prop) b S,
    (forall C, In C (components_of S) -> (no_generics C = true /\ plain_owners C = true)
        \/ (exists q, C = TypeVariable (mkGenericRef None true q []) /\ (P q = true -> R (mkGenericRef None true q [])))) ->
    vars_in P S = true ->
    (forall q, P q = true -> R (mkGenericRef None false q [])) ->
    ((forall C, In C (components_of S) -> args_plain C = true) \/ (forall gm nn q, P q = true -> R (mkGenericRef gm nn q []))) ->
    (forall q, P q = true -> ownership_bound b (parameter_ownership q) = true) ->
    refs_in b R (to_generic S).
Proof.
    intros P R b S Hc Hv HR Hcase Hb.
    assert (Hone: forall C, In C (components_of S) -> vars_in P C = true -> refs_in b R (to_generic C)).
    { intros C HC HvC. destruct (Hc C HC) as [[H1 H2]|[q [-> Hq]]].
      - destruct Hcase as [Hpl|Hany]; [exact (refs_of_vars P R b C H1 HvC (plain_owners_in _ C H2) (Hpl C HC) HR Hb)|].
        exact (refs_of_vars_any P R b C H1 HvC (plain_owners_in _ C H2) Hany Hb).
      - cbn [vars_in] in HvC. rewrite andb_true_r in HvC. exact (Hq HvC). }
    clear Hc Hcase. destruct (static_shape S) as [[E Ei]|[[cs [-> _]]|[cs [-> _]]]].
    { rewrite (components_of_none S Ei) in Hone. exact (Hone S (or_introl eq_refl) Hv). }
    all: cbn [to_generic refs_in]; change (forallb (vars_in P) cs = true) in Hv; cbn [components_of] in Hone;
        (induction cs as [|c cs IHc]; [exact I|]; simpl in Hv; apply andb_true_iff in Hv; destruct Hv as [Hv1 Hv2];
         split; [exact (Hone c (or_introl eq_refl) Hv1)|exact (IHc Hv2 (fun C HC => Hone C (or_intror HC)))]).
Qed.

(* What takes a type, made nullable, takes it without null *)
Lemma rewrap_takes: forall f x a, in_fragment env x = true -> in_fragment env a = true ->
    unify env f (rewrap_nullable x) a (Ongoing []) = Some (Ongoing []) ->
    exists f', unify env f' x (without_null env a) (Ongoing []) = Some (Ongoing []).
Proof.
    intros f x a Hx Ha H. destruct (fragment_cases env x Hx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        cbn [rewrap_nullable] in H; (destruct f as [|f]; [discriminate H|]); rewrite (unify_nullable_target env f _ _ [] Ha) in H.
    - exists f. exact H.
    - exists (S f). rewrite (unify_nullable_target env f _ _ [] (in_fragment_without_null env a Ha)), (without_null_twice_any env). exact H.
Qed.


Lemma not_in_fragment: forall S, no_vars S = false -> in_fragment env S = false.
Proof. intros S E. destruct (in_fragment env S) eqn:Ef; [|reflexivity]. rewrite (in_fragment_no_vars env S Ef) in E. exact E. Qed.

(* An intersection, nullable or not, isn't a type of the parameters *)
Lemma ifrag_inter: forall S cs, inter_of S = Some cs -> ifrag env S = false.
Proof.
    intros [| [| | | | | |?] | | | | |?] cs E; try discriminate E; unfold ifrag; cbn [no_generics is_class]; apply andb_false_r.
Qed.

(* A narrowed type variable among the components of a bound: the bound is neither a class type nor a
   type of the parameters *)
Lemma narrowed_component: forall S q, In (TypeVariable (mkGenericRef None true q [])) (components_of S) ->
    in_fragment env S = false /\ ifrag env S = false.
Proof.
    intros S q H. destruct (inter_of S) as [cs|] eqn:Ei.
    - split; [destruct S as [| [| | | | | |?] | | | | |?]; try discriminate Ei; reflexivity|exact (ifrag_inter S cs Ei)].
    - rewrite (components_of_none S Ei) in H. destruct H as [->|[]]. split; [reflexivity|].
      unfold ifrag. cbn [no_generics]. apply andb_false_r.
Qed.

(* The type parameters a type of the parameters mentions, as those of a caller (WithinBounds.mentions_only) *)
Lemma mentions_of_vars: forall ps (U: TypeParameterId -> Prop) (P: TypeParameterId -> bool) t,
    no_generics t = true -> vars_in P t = true -> plain_owners t = true ->
    (forall q, P q = true -> In q ps /\ U q) -> mentions_only_h ps U (to_generic t).
Proof.
    intros ps U P. fix IH 1. intros [m c args|n|g|me msg|v o n|[[gm|] [|] q [|w ws]]|cs] Hn Hv Ho HP;
        simpl in Hn, Hv, Ho |- *; try discriminate Hn; try exact I.
    - induction args as [|a args IHa]; [exact I|]. simpl in Hn, Hv, Ho |- *. apply andb_true_iff in Hn, Hv, Ho.
      exact (conj (IH a (proj1 Hn) (proj1 Hv) (proj1 Ho) HP) (IHa (proj2 Hn) (proj2 Hv) (proj2 Ho))).
    - apply andb_true_iff in Hn. exact (IH n (proj2 Hn) Hv Ho HP).
    - apply andb_true_iff in Ho. destruct Ho as [Ho1 Ho2]. split; [intros q' E; subst o; cbn in Ho1; discriminate Ho1|].
      apply orb_true_iff in Hn. destruct Hn as [Hn|Hn]; [exact (IH n Hn Hv Ho2 HP)|]. clear IH.
      destruct n as [|[| | | | |[gm nn q []]|]| | | |[gm nn q []]|]; try discriminate Hn; simpl in Hv |- *;
          rewrite andb_true_r in Hv; destruct (HP q Hv) as [Hq Hu]; exact (conj Hq (conj eq_refl Hu)).
    - rewrite andb_true_r in Hv. destruct (HP q Hv) as [Hq Hu]. exact (conj Hq (conj eq_refl Hu)).
Qed.

Lemma mentions_of_static: forall ps (U: TypeParameterId -> Prop) (P: TypeParameterId -> bool) S,
    (forall C, In C (components_of S) -> (no_generics C = true /\ plain_owners C = true)
        \/ (exists q, C = TypeVariable (mkGenericRef None true q []))) ->
    vars_in P S = true -> (forall q, P q = true -> In q ps /\ U q) -> mentions_only_h ps U (to_generic S).
Proof.
    intros ps U P S Hc Hv HP.
    assert (Hone: forall C, In C (components_of S) -> vars_in P C = true -> mentions_only_h ps U (to_generic C)).
    { intros C HC HvC. destruct (Hc C HC) as [[H1 H2]|[q ->]].
      - exact (mentions_of_vars ps U P C H1 HvC H2 HP).
      - cbn [vars_in] in HvC. rewrite andb_true_r in HvC. destruct (HP q HvC) as [Hq Hu].
        cbn [to_generic mentions_only_h param_of variables_of]. exact (conj Hq (conj eq_refl Hu)). }
    clear Hc. destruct (static_shape S) as [[E Ei]|[[cs [-> _]]|[cs [-> _]]]].
    { rewrite (components_of_none S Ei) in Hone. exact (Hone S (or_introl eq_refl) Hv). }
    all: cbn [to_generic mentions_only_h]; change (forallb (vars_in P) cs = true) in Hv; cbn [components_of] in Hone;
        (induction cs as [|c cs IHc]; [exact I|]; simpl in Hv; apply andb_true_iff in Hv; destruct Hv as [Hv1 Hv2];
         split; [exact (Hone c (or_introl eq_refl) Hv1)|exact (IHc Hv2 (fun C HC => Hone C (or_intror HC)))]).
Qed.

Section Invocation.

Variables xfrag bfrag: EType -> Prop.
Hypothesis types: inference_types env xfrag bfrag.
Hypothesis supertype_of_classes: closest_common_supertype_of_classes env.
Let xfrag_gfrag := it_xfrag_gfrag env xfrag bfrag types.
Let in_fragment_bfrag := it_in_fragment_bfrag env xfrag bfrag types.

(* The final value of the variable p *)
Definition final_of (U: VariableStates) (p: TypeParameterId): EType :=
    match lookup_state U p with Some st => final_value env st | None => bottom_type end.

(* The static upper bound S of the type parameter p, one of vars: its declared bound with type
   variables in place of the type parameters; of the types of the parameters, without ownerships of
   type parameters, a type variable of a mutability given to it, narrowed or made nullable among them
   (pfrag), or an intersection, nullable or not, of components of ifrag or narrowed type variables
   (compfrag: `A & Comparable<T>`, `A? & U?`, `A & U!`), assigned as one mutability, as ofComponents makes them; where it has no type
   variables, a class type, or an intersection of class types, nullable or not, among the bounds *)
Definition static_bound (vars: list (TypeParameterId * EType)) (p: TypeParameterId) (S: EType): Prop :=
    to_generic S = parameter_bound env p
    /\ (forall C, In C (intersected_components S) -> pfrag env C = true /\ plain_owners C = true)
    /\ vars_in (fun q => static_vars env p q && existsb (param_eqb q) (map fst vars)) S = true
    /\ (no_vars S = true -> in_fragment env S = true
        \/ (bfrag S /\ exists cs, (S = Intersection cs \/ S = Nullable (Intersection cs)) /\ class_components env cs = true))
    /\ (forall cs, inter_of S = Some cs -> (forall C, In C cs -> compfrag env C = true)
        /\ components_sfrag env (map to_generic cs) = true)
    /\ (forall cs, inter_of S = Some cs -> forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)).

(* A type parameter with a static upper bound starts inference as unify works with it *)
Lemma static_initial_ok: forall vars p S, static_bound vars p S -> initial_ok env xfrag bfrag p S.
Proof.
    intros vars p S [Hg [Hcomp [Hsv [Hcl [Hics0 Hun0]]]]] s. cbn zeta.
    cbn [upper_bound lower_bound is_exact is_capturable static_upper_bound].
    assert (HpoS: plain_owners S = true).
    { destruct (static_shape S) as [[E _]|[[cs [-> _]]|[cs [-> _]]]]; [|reflexivity|reflexivity].
      rewrite E in Hcomp. exact (proj2 (Hcomp S (or_introl eq_refl))). }
    assert (Hsv': vars_in (static_vars env p) S = true)
        by (apply (vars_in_mono _ _ (fun q E => proj1 (proj1 (andb_true_iff _ _) E)) _ Hsv)).
    destruct (no_vars S) eqn:Ens.
    - rewrite (initial_closed S Ens).
      split; [exact Ens|]. split; [reflexivity|]. split; [|exact Hsv'].
      intros _. split; [reflexivity|]. split.
      { destruct (Hcl eq_refl) as [Hfs|[_ [cs [Ecs Hcc]]]]; [exists 2; apply (below_all env wf [] S 2 Hfs); lia|].
        (* an intersection of class types: Nothing is below each component *)
        destruct (class_components_facts env cs Hcc) as [_ Hcls].
        assert (Hb: unify env 3 (Intersection cs) bottom_type (Ongoing []) = Some (Ongoing [])).
        { apply (inter_takes env 2 cs bottom_type [] Hcc (bottom_in_fragment env wf) eq_refl).
          intros c Hc. apply (below_all env wf [] c 2 (proj2 (Hcls c Hc))). lia. }
        destruct Ecs as [-> | ->]; [exists 3; exact Hb|exists 4; unfold bottom_type; rewrite unify_nullable_class; exact Hb]. }
      split; [destruct (Hcl eq_refl) as [Hfs|[HbS _]]; [exact (in_fragment_bfrag _ Hfs)|exact HbS]|]. split; [exact (in_fragment_bfrag _ (bottom_in_fragment env wf))|].
      unfold static_ok. cbn [static_upper_bound]. rewrite Ens. intros x f _ Ex; exists f; exact Ex.
    - unfold initial_upper_bound. rewrite Ens.
      split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hsv'].
      intros _. split; [reflexivity|]. split; [exists 2; apply (below_all env wf [] top_type 2 (top_in_fragment env wf)); lia|].
      split; [exact (in_fragment_bfrag _ (top_in_fragment env wf))|]. split; [exact (in_fragment_bfrag _ (bottom_in_fragment env wf))|].
      unfold static_ok. cbn [static_upper_bound lower_bound]. rewrite Ens.
      split; [exact (bottom_in_afrag env wf)|]. split; [reflexivity|].
      split; [intros C HC; exact (proj1 (Hcomp C HC))|]. split; [exact HpoS|].
      split; [split|].
      { intros cs Ecs. split; [exact (proj1 (Hics0 cs Ecs))|]. split; [exact (proj2 (Hics0 cs Ecs))|]. split; [exact (Hun0 cs Ecs)|].
        (* the components at the top of the bound are of a lower rank: none is the variable itself *)
        intros g Hg' Ep. pose proof (wf_bounds_ranked env wf p) as Hrk. rewrite <- Hg in Hrk.
        destruct S as [| [| | | | | |cs'] | | | | |cs']; try discriminate Ecs; injection Ecs as ->;
        cbn [to_generic ranked_below] in Hrk;
        (change (forallb (ranked_below env (parameter_rank env p)) (map to_generic cs) = true) in Hrk;
         rewrite forallb_forall in Hrk; pose proof (Hrk _ (in_map to_generic _ _ Hg')) as Hrc;
         destruct g as [gm nn q vs]; cbn [to_generic ranked_below] in Hrc; unfold rank_of in Hrc; cbn [param_of] in Hrc, Ep;
         apply Nat.ltb_lt in Hrc; subst q; lia). }
      { (* nor is the variable as the whole bound *)
        intros gm nn q Eq Ep. pose proof (wf_bounds_ranked env wf p) as Hrk. rewrite <- Hg in Hrk. subst q.
        destruct Eq as [-> | ->]; cbn [to_generic ranked_below] in Hrk; unfold rank_of in Hrk; cbn [param_of] in Hrk;
            apply Nat.ltb_lt in Hrk; lia. }
      intros E. change (class_eqb nothing nothing = false) in E. rewrite class_eqb_refl in E. discriminate E.
Qed.

(* How the type parameter p, with the static upper bound S, is bound in b, at the variable states U
   inference ends with: to a type argument of an exact ownership, of the types variables are replaced
   with, that fits the state p ends with. Bound exactly, p has a class type as its bound, and the type
   argument is within it; otherwise its state keeps S, and where S has type variables, the type
   argument is the lower bound, checked against S *)
Definition binds_var (U: VariableStates) (b: Bindings) (p: TypeParameterId) (S: EType): Prop :=
    exists o x st, lookup_binding b p = Some (TypeArgument invariant o x) /\ is_exact_ownership o = true /\ xfrag x
        /\ lookup_state U p = Some st /\ fits env st o x
        /\ if is_exact st then no_vars S = true /\ exists f, unify env f S x (Ongoing []) = Some (Ongoing [])
           else static_upper_bound st = S
               /\ (no_vars S = false -> x = lower_bound st /\ is_non_nullable_nothing env (lower_bound st) = false).

(* The type p is replaced with *)
Definition value_of (b: Bindings) (p: TypeParameterId): EType :=
    match lookup_binding b p with Some (TypeArgument _ _ x) => x | _ => bottom_type end.

(*
 * Bindings of the type parameters of vars as binds_var has them satisfy the variable states, and are
 * within the declared bounds, instantiated with them; and they bind the types that mention only those
 * type parameters. Rank by rank: the bound of a type parameter mentions those of a lower rank, and
 * the parameter itself. Where a bound is neither a class type nor a type of the parameters (ifrag): an
 * intersection, or a type variable of a mutability given to it, narrowed or made nullable, that takes
 * the bindings to be class types: then every reference to the type parameters is within its bound as
 * those of a caller are (WithinBounds.param_refs).
 *)
Lemma bindings_within: forall vars U b (extra: bool),
    (forall p S, In (p, S) vars -> static_bound vars p S) ->
    wf_states env xfrag bfrag U ->
    (forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars) ->
    (forall p S, In (p, S) vars -> binds_var U b p S) ->
    ((extra = true \/ exists p S, In (p, S) vars /\ in_fragment env S = false /\ (ifrag env S = false \/ args_plain S = false)) ->
        bindings_in_fragment env b) ->
    satisfies env xfrag b U
    /\ exists K, (forall p S, In (p, S) vars ->
            unify env K (inst_nested env b (parameter_bound env p)) (value_of b p) (Ongoing []) = Some (Ongoing []))
        /\ forall P, pfrag env P = true -> (args_plain P = true \/ extra = true) ->
            vars_in (fun q => existsb (param_eqb q) (map fst vars)) P = true ->
            owners_in (fun q => existsb (param_eqb q) (map fst vars)) P = true -> bound_in env b K [] (pgeneric P) = true.
Proof.
    intros vars U b extra Hst HwfU Hdom Hvar Hclass.
    set (ps := map fst vars) in *.
    assert (Hval: forall p S, In (p, S) vars ->
        exists o, lookup_binding b p = Some (TypeArgument invariant o (value_of b p)) /\ is_exact_ownership o = true /\ xfrag (value_of b p)).
    { intros p S Hin. destruct (Hvar p S Hin) as [o [x [st [Hl [Ho [Hx _]]]]]]. exists o. unfold value_of. rewrite Hl. auto. }
    assert (Hps: forall q, existsb (param_eqb q) ps = true -> exists S, In (q, S) vars).
    { intros q E. apply existsb_exists in E. destruct E as [q' [Hq' Eq]]. apply param_eqb_eq in Eq. subst q'.
      apply in_map_iff in Hq'. destruct Hq' as [[q1 S] [Hfst Hin]]. simpl in Hfst. subst q1. exists S. exact Hin. }
    (* the bindings satisfy the states *)
    assert (Hsat: satisfies env xfrag b U).
    { intros q o x Eq. destruct (Hdom q _ Eq) as [S Hin]. destruct (Hvar q S Hin) as [o' [x' [st [Hl [_ [Hx [HlU [Hfit _]]]]]]]].
      rewrite Hl in Eq. injection Eq as Eo Ex. subst o' x'. split; [exact Hx|]. exists st. split; [exact HlU|exact Hfit]. }
    (* bound to type arguments that aren't loose, nor of type arguments *)
    assert (Hpb: plain_bindings b).
    { intros q a Eq. destruct (Hdom q a Eq) as [S Hin]. destruct (Hvar q S Hin) as [o [x [st [Hl [Ho [Hx _]]]]]].
      rewrite Hl in Eq. injection Eq as <-. split; [destruct o; try reflexivity; discriminate Ho|].
      exists o, x. split; [reflexivity|].
      pose proof (xfrag_gfrag _ Hx) as Hg.
      destruct (gfrag_cases env _ Hg) as [[m [c [args E]]]|[[n0 [E [Hnn _]]]|[[gm [nn [q' [vs [E _]]]]]|[cs E]]]]; rewrite E;
          split; try reflexivity; intros z Ez; try discriminate Ez.
      injection Ez as <-. destruct n0; try reflexivity; discriminate Hnn. }
    assert (Hbv: forall t, vars_in (fun q => existsb (param_eqb q) ps) t = true -> bound_vars b t = true).
    { intros t Ht. apply vars_in_bound_vars. apply (vars_in_mono (fun q => existsb (param_eqb q) ps)); [|exact Ht].
      intros q E. destruct (Hps q E) as [S Hin]. destruct (Hval q S Hin) as [o [Hl _]]. unfold bound_in_b. rewrite Hl. reflexivity. }
    (* whether a bound is neither a class type nor a type of the parameters: then the bindings are class types *)
    set (Np := extra || existsb (fun v => negb (in_fragment env (snd v)) && negb (ifrag env (snd v) && args_plain (snd v))) vars).
    assert (HNp: Np = true -> bindings_in_fragment env b).
    { intros E. apply Hclass. unfold Np in E. apply orb_true_iff in E. destruct E as [E|E]; [left; exact E|right].
      apply existsb_exists in E. destruct E as [[q S] [Hin E]]. cbn [snd] in E.
      apply andb_true_iff in E. destruct E as [E1 E2]. apply negb_true_iff in E1, E2. exists q, S. split; [exact Hin|]. split; [exact E1|].
      apply andb_false_iff in E2. exact E2. }
    assert (HNp': forall q S, In (q, S) vars -> in_fragment env S = false -> ifrag env S = false -> Np = true).
    { intros q S Hin E1 E2. unfold Np. apply orb_true_iff. right. apply existsb_exists. exists (q, S). split; [exact Hin|].
      cbn [snd]. rewrite E1, E2. reflexivity. }
    (* a reference in a type argument, of a mutability given to it or narrowed *)
    assert (HNpa: forall q S, In (q, S) vars -> args_plain S = false -> Np = true).
    { intros q S Hin E. unfold Np. apply orb_true_iff. right. apply existsb_exists. exists (q, S). split; [exact Hin|].
      cbn [snd]. rewrite (args_plain_not_in_fragment S E), E, andb_false_r. reflexivity. }
    assert (HNpx: extra = true -> Np = true) by (intros E; unfold Np; rewrite E; reflexivity).
    assert (HNpf: Np = false -> forall q S, In (q, S) vars -> args_plain S = true).
    { intros EN q S Hin. destruct (args_plain S) eqn:E; [reflexivity|]. rewrite (HNpa q S Hin E) in EN. discriminate EN. }
    (* the references to the type parameters of a rank below r: plain, or of any mutability and `!` where a
       bound isn't a type of the parameters *)
    set (R := fun r g => exists q S gm nn, g = mkGenericRef gm nn q [] /\ In (q, S) vars /\ parameter_rank env q < r
        /\ (gm = None /\ nn = false \/ Np = true)).
    assert (Rplain: forall r q S, In (q, S) vars -> parameter_rank env q < r -> R r (mkGenericRef None false q [])).
    { intros r q S Hin Hr. exists q, S, None, false. split; [reflexivity|]. split; [exact Hin|]. split; [exact Hr|].
      left; split; reflexivity. }
    assert (Hown: forall q, existsb (param_eqb q) ps = true -> ownership_bound b (parameter_ownership q) = true).
    { intros q E. destruct (Hps q E) as [S Hin]. destruct (Hval q S Hin) as [o [Hl [Ho _]]]. cbn [ownership_bound]. rewrite Hl. exact Ho. }
    (* the references of a static upper bound *)
    assert (Hstatic: forall r q S, In (q, S) vars -> parameter_rank env q < r -> refs_in b (R r) (to_generic S)).
    { intros r q S Hin Hr. destruct (Hst q S Hin) as [_ [Hcomp [Hsv [_ [Hics _]]]]].
      assert (HP: forall q', static_vars env q q' && existsb (param_eqb q') ps = true ->
          exists S', In (q', S') vars /\ parameter_rank env q' < r).
      { intros q' E. apply andb_true_iff in E. destruct E as [E1 E2]. destruct (Hps q' E2) as [S' Hin']. exists S'. split; [exact Hin'|].
        unfold static_vars in E1. apply orb_true_iff in E1. destruct E1 as [E1|E1]; [apply param_eqb_eq in E1; subst q'; exact Hr|].
        unfold rank_below in E1. apply Nat.ltb_lt in E1. lia. }
      assert (Hplain: (forall C, In C (components_of S) -> compfrag env C = true) -> refs_in b (R r) (to_generic S)).
      { intros Hif. apply (refs_of_static (fun q' => static_vars env q q' && existsb (param_eqb q') ps) (R r) b S); [| exact Hsv | | |].
        - intros C HC. destruct (compfrag_cases env C (Hif C HC)) as [HCi|[q' [-> _]]].
          + left. exact (conj (ifrag_no_generics env C HCi) (components_of_owners S (fun C' HC' => proj2 (Hcomp C' HC')) C HC)).
          + (* a narrowed type variable: then the references are of any mutability and `!` *)
            right. exists q'. split; [reflexivity|]. intros E. destruct (HP q' E) as [S' [Hin' Hr']].
            destruct (narrowed_component S q' HC) as [Hf1 Hf2].
            exists q', S', None, true. split; [reflexivity|]. split; [exact Hin'|]. split; [exact Hr'|right; exact (HNp' q S Hin Hf1 Hf2)].
        - intros q' E. destruct (HP q' E) as [S' [Hin' Hr']]. exact (Rplain r q' S' Hin' Hr').
        - destruct (Bool.bool_dec Np true) as [EN|EN];
              [right|left; apply not_true_is_false in EN; exact (args_plain_components S (HNpf EN q S Hin))].
          intros gm nn q' E. destruct (HP q' E) as [S' [Hin' Hr']].
          exists q', S', gm, nn. split; [reflexivity|]. split; [exact Hin'|]. split; [exact Hr'|right; exact EN].
        - intros q' E. apply andb_true_iff in E. exact (Hown q' (proj2 E)). }
      destruct (static_shape S) as [[E Ei]|[[cs [Ecs _]]|[cs [Ecs _]]]];
          [|apply Hplain; rewrite Ecs; exact (proj1 (Hics cs (f_equal inter_of Ecs)))|apply Hplain; rewrite Ecs; exact (proj1 (Hics cs (f_equal inter_of Ecs)))].
      destruct (ifrag env S) eqn:Ef; [apply Hplain; rewrite (components_of_none S Ei); intros C [<-|[]]; unfold compfrag; rewrite Ef; reflexivity|].
      (* a type variable of a mutability given to it, narrowed or made nullable *)
      rewrite E in Hcomp.
      destruct (pfrag_cases env S (proj1 (Hcomp S (or_introl eq_refl)))) as [Hif|[[gm [nn [q' [ES _]]]]|[gm [nn [q' [ES _]]]]]];
          [rewrite Ef in Hif; discriminate Hif| |];
          (pose proof (HNp' q S Hin ltac:(rewrite ES; reflexivity) Ef) as HN; subst S;
           cbn [vars_in] in Hsv; rewrite andb_true_r in Hsv; destruct (HP q' Hsv) as [S' [Hin' Hr']];
           cbn [to_generic refs_in]; exists q', S', gm, nn; split; [reflexivity|]; split; [exact Hin'|]; split; [exact Hr'|right; exact HN]). }
    assert (Hclose: forall r g, R r g -> refs_in b (R r) (effective_bound env g) /\ refs_in b (R r) (parameter_bound env (param_of g))).
    { intros r g [q [S [gm [nn [-> [Hin [Hr Hs]]]]]]]. cbn [param_of].
      destruct (Hst q S Hin) as [Hg _]. rewrite <- Hg.
      pose proof (Hstatic r q S Hin Hr) as H. split; [|exact H].
      destruct Hs as [[-> ->]|HN]; [rewrite (effective_bound_plain env ranked), <- Hg; exact H|].
      (* of any mutability and `!` *)
      assert (Hadj: forall gm nn gm' nn' q vs, R r (mkGenericRef gm nn q vs) -> R r (mkGenericRef gm' nn' q vs)).
      { intros gm1 nn1 gm2 nn2 q1 vs [q2 [S2 [gm3 [nn3 [E [Hin2 [Hr2 _]]]]]]]. injection E as -> -> -> ->.
        exists q2, S2, gm2, nn2. split; [reflexivity|]. split; [exact Hin2|]. split; [exact Hr2|right; exact HN]. }
      rewrite (effective_bound_eq env ranked). cbn [with_type_variables variables_of given_mutability is_narrowed param_of]. rewrite <- Hg.
      destruct (refs_in_adjust env b (R r) Hadj _ H) as [Hm Hn].
      destruct gm as [m|], nn; cbn iota; [exact (proj2 (refs_in_adjust env b (R r) Hadj _ (Hm m)))|exact (Hm m)|exact Hn|exact H]. }
    (* the references of R r bound, where the bindings of a rank below r are within their bounds *)
    assert (HR: forall r K, (forall p S, In (p, S) vars -> parameter_rank env p < r ->
            unify env K (inst_nested env b (parameter_bound env p)) (value_of b p) (Ongoing []) = Some (Ongoing [])) ->
        exists K', K <= K' /\ forall g, R r g -> binds_ref env b K' [] g = true /\ variables_of g = []).
    { intros r K Hr. destruct (Bool.bool_dec Np true) as [EN|EN]; [|apply not_true_is_false in EN].
      2:{ (* plain *)
          exists K. split; [lia|]. intros g [q [S [gm [nn [-> [Hin [Hrq [[-> ->]|HN]]]]]]]]; [|rewrite EN in HN; discriminate HN].
          split; [|reflexivity]. unfold binds_ref. cbn [param_of].
          destruct (Hval q S Hin) as [o [Hl [Ho Hx]]]. rewrite Hl, Ho. cbn [andb]. rewrite (xfrag_gfrag _ Hx). cbn [andb].
          unfold respects, inst_ref, inst_fit. cbn [given_mutability is_narrowed]. rewrite (effective_bound_plain env ranked).
          rewrite (Hr q S Hin Hrq). reflexivity. }
      (* the bindings are class types: as those of the type parameters of a caller (WithinBounds.param_refs) *)
      pose proof (HNp EN) as Hbf.
      set (ps_r := map fst (filter (fun v => Nat.ltb (parameter_rank env (fst v)) r) vars)).
      assert (Hin_r: forall q, In q ps_r <-> exists S, In (q, S) vars /\ parameter_rank env q < r).
      { intros q. unfold ps_r. rewrite in_map_iff. split.
        - intros [[q1 S] [E Hin]]. cbn [fst] in E. subst q1. apply filter_In in Hin. destruct Hin as [Hin Hr'].
          cbn [fst] in Hr'. apply Nat.ltb_lt in Hr'. exists S. split; assumption.
        - intros [S [Hin Hr']]. exists (q, S). split; [reflexivity|]. apply filter_In. split; [exact Hin|apply Nat.ltb_lt; exact Hr']. }
      (* the declared bounds of those mention only them *)
      assert (Hmo: forall q S, In (q, S) vars -> parameter_rank env q < r -> mentions_only env ps_r (parameter_bound env q)).
      { intros q. remember (parameter_rank env q) as k eqn:Ek. revert q Ek. induction k as [k IHk] using lt_wf_ind.
        intros q -> S Hin Hrq. apply (param_mentions_only_iff env wf ps_r). unfold param_mentions_only.
        rewrite (through_param_eq env (mentions_only_h ps_r) True (wf_bounds_deep_ranked env wf) (mentions_only_h_agree env ps_r) q).
        destruct (Hst q S Hin) as [Hg [Hcomp [Hsv [_ [Hics _]]]]]. rewrite <- Hg.
        set (Uq := fun q' => if param_eqb q' q then True else through_param env (mentions_only_h ps_r) True q').
        assert (HU: forall q', static_vars env q q' && existsb (param_eqb q') ps = true -> In q' ps_r /\ Uq q').
        { intros q' E. apply andb_true_iff in E. destruct E as [E1 E2]. destruct (Hps q' E2) as [S' Hin'].
          unfold static_vars in E1. apply orb_true_iff in E1. destruct E1 as [E1|E1].
          - apply param_eqb_eq in E1. subst q'. split; [apply Hin_r; exists S; split; [exact Hin|exact Hrq]|].
            unfold Uq, param_eqb. rewrite Nat.eqb_refl. exact I.
          - unfold rank_below in E1. apply Nat.ltb_lt in E1. split; [apply Hin_r; exists S'; split; [exact Hin'|lia]|].
            unfold Uq. destruct (param_eqb q' q); [exact I|].
            change (param_mentions_only env ps_r q'). apply (param_mentions_only_iff env wf ps_r).
            exact (IHk _ E1 q' eq_refl S' Hin' ltac:(lia)). }
        assert (Hplain: (forall C, In C (components_of S) -> compfrag env C = true) -> mentions_only_h ps_r Uq (to_generic S)).
        { intros Hif. apply (mentions_of_static ps_r Uq (fun q' => static_vars env q q' && existsb (param_eqb q') ps) S); [|exact Hsv|exact HU].
          intros C HC. destruct (compfrag_cases env C (Hif C HC)) as [HCi|[q' [-> _]]]; [left|right; exists q'; reflexivity].
          exact (conj (ifrag_no_generics env C HCi) (components_of_owners S (fun C' HC' => proj2 (Hcomp C' HC')) C HC)). }
        destruct (static_shape S) as [[E Ei]|[[cs [Ecs _]]|[cs [Ecs _]]]];
            [|apply Hplain; rewrite Ecs; exact (proj1 (Hics cs (f_equal inter_of Ecs)))|apply Hplain; rewrite Ecs; exact (proj1 (Hics cs (f_equal inter_of Ecs)))].
        rewrite E in Hcomp.
        destruct (pfrag_cases env S (proj1 (Hcomp S (or_introl eq_refl)))) as [Hif|[[gm [nn [q' [-> _]]]]|[gm [nn [q' [-> _]]]]]];
            [apply Hplain; rewrite (components_of_none S Ei); intros C [<-|[]]; unfold compfrag; rewrite Hif; reflexivity| |];
            (cbn [vars_in] in Hsv; rewrite andb_true_r in Hsv; destruct (HU q' Hsv) as [Hq' Hu];
             cbn [to_generic mentions_only_h param_of variables_of]; exact (conj Hq' (conj eq_refl Hu))). }
      (* of the fragment at the top *)
      assert (Htf: forall q S, In (q, S) vars -> tfrag env (parameter_bound env q) = true).
      { intros q S Hin. destruct (Hst q S Hin) as [Hg [Hcomp [_ [_ [Hics _]]]]]. rewrite <- Hg.
        destruct (static_shape S) as [[E _]|[[cs [-> _]]|[cs [-> _]]]]; [|exact (proj2 (Hics cs eq_refl))|exact (proj2 (Hics cs eq_refl))].
        rewrite E in Hcomp.
        destruct (pfrag_cases env S (proj1 (Hcomp S (or_introl eq_refl)))) as [Hif|[[gm [nn [q' [-> [Hs' _]]]]]|[gm [nn [q' [-> [Hs' _]]]]]]];
            [|exact Hs'|exact Hs'].
        pose proof (ifrag_sfrag env S Hif) as Hs.
        destruct (ifrag_cases env wf S Hif) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[q'' [-> _]]]]]; exact Hs. }
      assert (Hwithin: forall q, In q ps_r -> exists o x, lookup_binding b q = Some (TypeArgument invariant o x)
          /\ is_exact_ownership o = true
          /\ exists f, unify env f (inst_nested env b (parameter_bound env q)) x (Ongoing []) = Some (Ongoing [])).
      { intros q Hq. apply Hin_r in Hq. destruct Hq as [S [Hin Hrq]]. destruct (Hval q S Hin) as [o [Hl [Ho _]]].
        exists o, (value_of b q). split; [exact Hl|]. split; [exact Ho|]. exists K. exact (Hr q S Hin Hrq). }
      assert (Hdecl: forall q, In q ps_r -> tfrag env (parameter_bound env q) = true
          /\ built env (parameter_bound env) (parameter_bound env q) /\ mentions_only env ps_r (parameter_bound env q)).
      { intros q Hq. apply Hin_r in Hq. destruct Hq as [S [Hin Hrq]].
        split; [exact (Htf q S Hin)|]. split; [exact I|exact (Hmo q S Hin Hrq)]. }
      destruct (uniform_fuel_list ps_r (fun K' q => forall gm nn, binds_ref env b K' [] (mkGenericRef gm nn q []) = true)) as [K1 HK1].
      { intros f f' q Hle H gm nn. exact (binds_ref_mono env b f f' _ Hle (H gm nn)). }
      { exact (param_refs env wf b Hbf (parameter_bound env) ps_r Hwithin Hdecl (fun _ => eq_refl)). }
      exists (max K K1). split; [lia|]. intros g [q [S [gm [nn [-> [Hin [Hrq _]]]]]]]. split; [|reflexivity].
      apply (binds_ref_mono env b K1); [lia|]. apply HK1. apply Hin_r. exists S. split; assumption. }
    set (rmax := S (list_max (map (fun v => parameter_rank env (fst v)) vars))).
    assert (Hrmax: forall p S, In (p, S) vars -> parameter_rank env p < rmax).
    { intros p S Hin. unfold rmax.
      assert (H: Forall (fun k => k <= list_max (map (fun v => parameter_rank env (fst v)) vars)) (map (fun v => parameter_rank env (fst v)) vars))
          by (apply list_max_le; lia).
      rewrite Forall_forall in H. specialize (H (parameter_rank env p) (in_map (fun v => parameter_rank env (fst v)) _ _ Hin)). lia. }
    (* the bindings exist, also for the type parameters in the bounds *)
    assert (Hbex: forall t, refs_in b (R rmax) t -> bex env b t = true).
    { apply bex_of_refs. intros g Hg. pose proof (proj2 (Hclose rmax g Hg)) as Hpb'.
      destruct Hg as [q [S [gm [nn [-> [Hin [Hrq _]]]]]]]. split; [|split; [reflexivity|exact Hpb']].
      unfold has_binding. cbn [param_of]. destruct (Hval q S Hin) as [o [Hl [Ho Hx]]]. rewrite Hl, Ho. cbn [andb].
      exact (xfrag_gfrag _ Hx). }
    (* the bindings are within their bounds, rank by rank *)
    assert (Hwithin: forall r, exists K, forall p S, In (p, S) vars -> parameter_rank env p < r ->
        unify env K (inst_nested env b (parameter_bound env p)) (value_of b p) (Ongoing []) = Some (Ongoing [])).
    { induction r as [|r [Kr IHr]].
      { exists 0. intros p S _ H. lia. }
      destruct (HR r Kr IHr) as [Kr' [_ HRr]].
      assert (Hp: forall p S, In (p, S) vars -> parameter_rank env p = r ->
          exists f, unify env f (inst_nested env b (parameter_bound env p)) (value_of b p) (Ongoing []) = Some (Ongoing [])).
      { intros p S Hin Hrp. destruct (Hvar p S Hin) as [o [x [st [Hl [Ho [Hx [HlU [Hfit Hcase]]]]]]]].
        assert (Ev: value_of b p = x) by (unfold value_of; rewrite Hl; reflexivity). rewrite Ev. clear Ev.
        destruct (Hst p S Hin) as [Hg [Hcomp [Hsv [Hcl [Hics _]]]]].
        (* without type variables as the declared bound: a class type, its instance itself; or an
           intersection of class types, of the instances of its components, themselves *)
        assert (Hclosed: no_vars S = true -> forall f, unify env f S x (Ongoing []) = Some (Ongoing []) ->
            exists f', unify env f' (inst_nested env b (parameter_bound env p)) x (Ongoing []) = Some (Ongoing [])).
        { intros Ens f Ef'. destruct (Hcl Ens) as [Hfs|[_ [cs [Ecs Hcc]]]].
          { destruct (static_shape S) as [[E _]|[[cs [-> _]]|[cs [-> _]]]]; [|discriminate Hfs|discriminate Hfs].
            rewrite E in Hcomp. destruct (Hcomp S (or_introl eq_refl)) as [Hpf Hpo].
            assert (Hif: ifrag env S = true).
            { destruct (pfrag_cases env S Hpf) as [H|[[? [? [? [-> _]]]]|[? [? [? [-> _]]]]]]; [exact H|cbn in Ens; discriminate Ens|cbn in Ens; discriminate Ens]. }
            pose proof (closed_of_ifrag S Hif Ens Hpo) as Hc.
            pose proof (ifrag_sfrag env S Hif) as Hsf. rewrite (to_generic_closed S Hc) in Hsf.
            rewrite <- Hg, (to_generic_closed S Hc), (inst_nested_closed env wf b 0 [] S Hsf Hc). exists f. exact Ef'. }
          (* an intersection of class types, nullable or not: the bindings are class types *)
          assert (HiS: inter_of S = Some cs) by (destruct Ecs as [-> | ->]; reflexivity).
          assert (Hbf: bindings_in_fragment env b).
          { apply Hclass. right. exists p, S. split; [exact Hin|]. split; [destruct Ecs as [-> | ->]; reflexivity|left; exact (ifrag_inter S cs HiS)]. }
          pose proof (Hbf p o x Hl) as HxF.
          destruct (class_components_facts env cs Hcc) as [_ Hcls].
          destruct (Hics cs HiS) as [Hif Hcs].
          assert (Hcomp1: forall c, In c cs -> ifrag env c = true /\ plain_owners c = true).
          { intros c Hc. split.
            { apply (compfrag_ifrag env c (Hif c Hc)). pose proof (proj1 (Hcls c Hc)) as Hk. destruct c; try discriminate Hk. reflexivity. }
            apply (components_of_owners S (fun C' HC' => proj2 (Hcomp C' HC'))). destruct Ecs as [-> | ->]; exact Hc. }
          assert (Hself: forall c, In c cs -> to_generic c = c /\ inst_nested env b c = c).
          { intros c Hc. destruct (Hcomp1 c Hc) as [Hic Hpc].
            pose proof (closed_of_ifrag c Hic (in_fragment_no_vars env _ (proj2 (Hcls c Hc))) Hpc) as Hcc'.
            pose proof (ifrag_sfrag env c Hic) as Hsc. rewrite (to_generic_closed c Hcc') in Hsc.
            split; [exact (to_generic_closed c Hcc')|exact (inst_nested_closed env wf b 0 [] c Hsc Hcc')]. }
          assert (Hmap: map to_generic cs = cs).
          { clear -Hself. induction cs as [|c cs IH]; [reflexivity|]. cbn [map]. rewrite (proj1 (Hself c (or_introl eq_refl))).
            rewrite IH; [reflexivity|]. intros c' Hc'. exact (Hself c' (or_intror Hc')). }
          rewrite Hmap in Hcs.
          assert (Htop: forall c, In c cs -> bound_in_top_h env b 0 [] (top_bound_in env b 0 []) c = true).
          { intros c Hc. pose proof (proj1 (Hcls c Hc)) as Hk. destruct c as [m cl args| | | | | |]; try discriminate Hk. reflexivity. }
          pose proof (Hstatic rmax p S Hin (Hrmax p S Hin)) as Hrefs.
          rewrite <- Hg. destruct Ecs as [ES|ES]; rewrite ES in Hrefs, Ef' |- *; cbn [to_generic] in Hrefs |- *; rewrite Hmap in Hrefs |- *.
          - destruct f as [|f]; [discriminate Ef'|].
            destruct (inter_accepts env wf f cs x [] [] Hcc HxF Ef') as [_ [_ Hall]].
            apply (below_intersection_instance b 0 cs x Hbf Hcs (Hbex _ Hrefs) Htop HxF).
            intros c Hc. exists f. rewrite (proj2 (Hself c Hc)). exact (Hall c Hc).
          - change (refs_in b (R rmax) (Intersection cs)) in Hrefs.
            destruct f as [|f]; [discriminate Ef'|]. rewrite (unify_nullable_target env f _ _ [] HxF) in Ef'.
            pose proof (in_fragment_without_null env x HxF) as HxF'.
            destruct f as [|f]; [discriminate Ef'|].
            destruct (inter_accepts env wf f cs _ [] [] Hcc HxF' Ef') as [_ [_ Hall]].
            destruct (below_intersection_instance b 0 cs _ Hbf Hcs (Hbex _ Hrefs) Htop HxF'
                (fun c Hc => ex_intro _ f (eq_ind_r (fun t => unify env f t _ (Ongoing []) = Some (Ongoing [])) (Hall c Hc) (proj2 (Hself c Hc)))))
                as [f' Hf'].
            exists (Nat.succ f'). change (inst_nested env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection cs))).
            exact (unify_rewrap_target env _ _ _ [] _ HxF Hf'). }
        case_eq (is_exact st); intros He; rewrite He in Hcase.
        { (* bound exactly: within the declared bound, without type variables *)
          destruct Hcase as [Ens [f Ef']]. exact (Hclosed Ens f Ef'). }
        destruct Hcase as [Hs Hlow].
        destruct (HwfU p st HlU) as [_ [_ [Hw _]]]. destruct (Hw He) as [_ [_ [_ [_ Hok]]]].
        unfold static_ok in Hok. rewrite Hs in Hok. case_eq (no_vars S); intros Ens; rewrite Ens in Hok.
        { (* a class type: the binding is below the upper bound, which is below it *)
          unfold fits in Hfit. rewrite He in Hfit. destruct Hfit as [_ [K2 E2]].
          destruct (Hok _ K2 Hx E2) as [f Ef']. rewrite Hs in Ef'. exact (Hclosed Ens f Ef'). }
        (* with type variables: the binding is the lower bound, checked against each component *)
        destruct (Hlow Ens) as [Exl Hnn]. subst x.
        destruct Hok as [HlA [HlC [_ [_ [Hform Hchk]]]]].
        unfold static_checked in Hchk. rewrite Hs in Hchk.
        (* checked against an intersection, the bindings are class types *)
        assert (Hbf0: (exists cs, inter_of S = Some cs) -> bindings_in_fragment env b).
        { intros [cs' Ecs]. apply Hclass. right. exists p, S. split; [exact Hin|]. split; [exact (not_in_fragment S Ens)|].
          left. exact (ifrag_inter S cs' Ecs). }
        assert (Hc: forall C, In C (intersected_components S) ->
            exists f, unify env f (inst_nested env b (to_generic C)) (lower_bound st) (Ongoing []) = Some (Ongoing [])).
        { intros C HC. destruct (Hcomp C HC) as [Hpf Hpo].
          pose proof (vars_in_intersected _ _ Hsv C HC) as HsvC.
          destruct (ifrag env C) eqn:Hif.
          2:{ (* a type variable of a mutability given to it, narrowed or made nullable, other than p, of a lower rank:
                 the whole bound, or a component of a nullable intersection, made nullable *)
              assert (Href: exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) \/ C = Nullable (TypeVariable (mkGenericRef gm nn q []))).
              { destruct (pfrag_cases env C Hpf) as [H|[[gm [nn [q [ES _]]]]|[gm [nn [q [ES _]]]]]];
                    [rewrite H in Hif; discriminate Hif|exists gm, nn, q; left; exact ES|exists gm, nn, q; right; exact ES]. }
              destruct Href as [gm [nn [q Eq]]].
              assert (Hq: q <> p /\ (gm = None /\ nn = false \/ Np = true)).
              { destruct (static_shape S) as [[E _]|[[cs [Ecs _]]|[cs [Ecs _]]]].
                - rewrite E in HC. destruct HC as [<-|[]]. split; [exact (proj2 Hform gm nn q Eq)|right].
                  exact (HNp' p S Hin (not_in_fragment S Ens) Hif).
                - (* a narrowed type variable, a component of an intersection *)
                  rewrite Ecs in HC, Hform. split; [|right; exact (HNp' p S Hin (not_in_fragment S Ens) (ifrag_inter S cs (f_equal inter_of Ecs)))].
                  destruct (proj1 Hform cs eq_refl) as [_ [_ [_ Hnp]]].
                  destruct Eq as [Eq|Eq]; subst C; [exact (Hnp _ HC)|].
                  pose proof (proj1 (Hics cs (f_equal inter_of Ecs)) _ HC) as Hic.
                  unfold compfrag, ifrag in Hic. cbn [no_generics is_class andb] in Hic. rewrite andb_false_r in Hic. discriminate Hic.
                - rewrite Ecs in HC, Hform. cbn [intersected_components] in HC. apply in_map_iff in HC. destruct HC as [c [Ec Hc']].
                  subst C. destruct Eq as [Eq|Eq]; [discriminate Eq|]. injection Eq as Ec. subst c.
                  split; [|right; exact (HNp' p S Hin (not_in_fragment S Ens) (ifrag_inter S cs (f_equal inter_of Ecs)))].
                  destruct (proj1 Hform cs eq_refl) as [_ [_ [_ Hnp]]]. exact (Hnp _ Hc'). }
              assert (Hpq: static_vars env p q && existsb (param_eqb q) ps = true)
                  by (destruct Eq as [-> | ->]; cbn [vars_in] in HsvC; rewrite andb_true_r in HsvC; exact HsvC).
              apply andb_true_iff in Hpq. destruct Hpq as [Hsq Hq']. destruct (Hps q Hq') as [S' Hin'].
              assert (Hrq: parameter_rank env q < r).
              { unfold static_vars in Hsq. apply orb_true_iff in Hsq. destruct Hsq as [Hsq|Hsq];
                    [apply param_eqb_eq in Hsq; destruct Hq as [Hq _]; contradiction|unfold rank_below in Hsq; apply Nat.ltb_lt in Hsq; lia]. }
              assert (HRq: R r (mkGenericRef gm nn q [])).
              { exists q, S', gm, nn. split; [reflexivity|]. split; [exact Hin'|]. split; [exact Hrq|exact (proj2 Hq)]. }
              pose proof (refs_bound_in env wf b Kr' (R r) HRr (Hclose r) (Generic (mkGenericRef gm nn q [])) HRq) as Hbc.
              specialize (Hchk Hnn C HC).
              destruct Eq as [ES|ES]; rewrite ES in Hchk |- *;
                  [rewrite (proj1 (candidate_reference env p (lower_bound st) gm nn q (proj1 Hq))) in Hchk
                  |rewrite (proj2 (candidate_reference env p (lower_bound st) gm nn q (proj1 Hq))) in Hchk];
                  destruct (Hchk b Kr' Hbc Hsat Hbf0) as [f Ef']; exists f; exact Ef'. }
          assert (HbvC: bound_vars b C = true)
              by (apply Hbv; apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ HsvC)).
          pose proof (with_candidate_ifrag env wf p _ HlA HlC C Hif) as Hwi.
          assert (Hbc: bound_in env b Kr' [] (to_generic (with_candidate env p (lower_bound st) C)) = true).
          { apply (refs_bound_in env wf b Kr' (R r) HRr (Hclose r)).
            set (Pc := fun q => (static_vars env p q && existsb (param_eqb q) ps) && negb (param_eqb q p)).
            assert (HPc: forall q, Pc q = true -> exists S', In (q, S') vars /\ parameter_rank env q < r).
            { intros q E. unfold Pc in E. apply andb_true_iff in E. destruct E as [E1 E3]. apply andb_true_iff in E1. destruct E1 as [E1 E2].
              destruct (Hps q E2) as [S' Hin']. exists S'. split; [exact Hin'|].
              unfold static_vars in E1. apply orb_true_iff in E1. destruct E1 as [E1|E1]; [rewrite E1 in E3; discriminate E3|].
              unfold rank_below in E1. apply Nat.ltb_lt in E1. lia. }
            assert (HoC: forall q, Pc q = true -> ownership_bound b (parameter_ownership q) = true).
            { intros q E. unfold Pc in E. apply andb_true_iff in E. destruct E as [E1 _]. apply andb_true_iff in E1. exact (Hown q (proj2 E1)). }
            destruct (Bool.bool_dec Np true) as [EN|EN]; [|apply not_true_is_false in EN].
            - apply (refs_of_vars_any Pc (R r) b).
              + exact (ifrag_no_generics env _ Hwi).
              + exact (candidate_vars env wf _ p _ C HsvC (in_fragment_no_vars env _ (proj1 (afrag_parts env _ HlA)))).
              + exact (plain_owners_in _ _ (plain_owners_candidate p _ HlA HlC C Hif Hpo)).
              + intros gm nn q E. destruct (HPc q E) as [S' [Hin' Hr']].
                exists q, S', gm, nn. split; [reflexivity|]. split; [exact Hin'|]. split; [exact Hr'|right; exact EN].
              + exact HoC.
            - apply (refs_of_vars Pc (R r) b).
              + exact (ifrag_no_generics env _ Hwi).
              + exact (candidate_vars env wf _ p _ C HsvC (in_fragment_no_vars env _ (proj1 (afrag_parts env _ HlA)))).
              + exact (plain_owners_in _ _ (plain_owners_candidate p _ HlA HlC C Hif Hpo)).
              + exact (args_plain_candidate p _ HlA HlC C Hif (args_plain_intersected S (HNpf EN p S Hin) C HC)).
              + intros q E. destruct (HPc q E) as [S' [Hin' Hr']]. exact (Rplain r q S' Hin' Hr').
              + exact HoC. }
          destruct (Hchk Hnn C HC b Kr' Hbc Hsat Hbf0) as [f Ef']. exists f.
          pose proof (bound_vars_candidate b p (lower_bound st) C (ifrag_no_generics env C Hif) HbvC
              (in_fragment_no_vars env _ (proj1 (afrag_parts env _ HlA)))) as Hbvc.
          unfold inst in Ef'. rewrite (inst_nested_plain b _ Hpb Hwi Hbvc) in Ef'.
          rewrite (candidate_instantiate b p o (lower_bound st) Hpb Hl HlA HlC C Hif Hpo HbvC) in Ef'.
          rewrite <- (inst_nested_plain b C Hpb Hif HbvC) in Ef'. exact Ef'. }
        rewrite <- Hg. destruct (static_shape S) as [[E _]|[[cs [-> E]]|[cs [-> E]]]].
        + rewrite E in Hc. exact (Hc S (or_introl eq_refl)).
        + (* an intersection: below the instance of each component, below that of the intersection *)
          pose proof (Hstatic rmax p _ Hin (Hrmax p _ Hin)) as Hrefs.
          change (refs_in b (R rmax) (Intersection (map to_generic cs))) in Hrefs.
          rewrite E in Hc, Hcomp. cbn [to_generic].
          assert (Hbf: bindings_in_fragment env b) by exact (Hbf0 (ex_intro _ cs eq_refl)).
          apply (below_intersection_instance b Kr' (map to_generic cs) (lower_bound st) Hbf (proj2 (Hics cs eq_refl)) (Hbex _ Hrefs)).
          * (* the components at the top of the bound: class types, and references of a lower rank *)
            pose proof (wf_bounds_ranked env wf p) as Hrk. rewrite <- Hg in Hrk. cbn [to_generic ranked_below] in Hrk.
            change (forallb (ranked_below env (parameter_rank env p)) (map to_generic cs) = true) in Hrk.
            rewrite forallb_forall in Hrk.
            intros c Hc'. pose proof (Hrk c Hc') as Hrc. apply in_map_iff in Hc'. destruct Hc' as [C [<- HC]].
            pose proof (proj1 (Hics cs eq_refl) C HC) as HCf.
            destruct (compfrag_cases env C HCf) as [Hif|[q [-> _]]].
            2:{ (* a narrowed type variable, of a lower rank *)
                cbn [to_generic ranked_below rank_of param_of] in Hrc |- *. apply Nat.ltb_lt in Hrc.
                pose proof (vars_in_intersected _ _ Hsv _ HC) as HsvC. cbn [vars_in] in HsvC.
                apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
                destruct (Hps q HsvC) as [S' Hin'].
                assert (HRq: R r (mkGenericRef None true q [])).
                { exists q, S', None, true. split; [reflexivity|]. split; [exact Hin'|].
                  split; [unfold rank_of in Hrc; cbn [param_of] in Hrc; lia|right].
                  exact (HNp' p _ Hin (not_in_fragment _ Ens) (ifrag_inter (Intersection cs) cs eq_refl)). }
                destruct (HRr _ HRq) as [Hbr _]. cbn [bound_in_top_h]. rewrite Hbr. cbn [andb no_type_variables variables_of].
                exact (refs_top env wf b Kr' (R r) HRr (Hclose r) _ HRq). }
            destruct (ifrag_cases env wf C Hif) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]]; try reflexivity.
            cbn [to_generic ranked_below rank_of param_of] in Hrc |- *. apply Nat.ltb_lt in Hrc.
            pose proof (vars_in_intersected _ _ Hsv _ HC) as HsvC. cbn [vars_in] in HsvC.
            apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
            destruct (Hps q HsvC) as [S' Hin'].
            assert (HRq: R r (mkGenericRef None false q []))
                by (apply (Rplain r q S' Hin'); unfold rank_of in Hrc; cbn [param_of] in Hrc; lia).
            destruct (HRr _ HRq) as [Hbr _]. cbn [bound_in_top_h]. rewrite Hbr. cbn [andb no_type_variables variables_of].
            exact (refs_top env wf b Kr' (R r) HRr (Hclose r) _ HRq).
          * exact (proj1 (afrag_parts env _ HlA)).
          * intros c Hc'. apply in_map_iff in Hc'. destruct Hc' as [C [<- HC]]. exact (Hc C HC).
        + (* a nullable intersection: the lower bound without null below that of the intersection *)
          pose proof (Hstatic rmax p _ Hin (Hrmax p _ Hin)) as Hrefs.
          change (refs_in b (R rmax) (Intersection (map to_generic cs))) in Hrefs.
          rewrite E in Hc, Hcomp. cbn [to_generic].
          assert (Hbf: bindings_in_fragment env b) by exact (Hbf0 (ex_intro _ cs eq_refl)).
          destruct (afrag_parts env _ HlA) as [HlF _].
          destruct (components_sfrag_facts env _ (proj2 (Hics cs eq_refl))) as [_ Hshape].
          assert (Hi: exists f, unify env f (inst_nested env b (Intersection (map to_generic cs))) (without_null env (lower_bound st)) (Ongoing [])
              = Some (Ongoing [])).
          { apply (below_intersection_instance b Kr' (map to_generic cs) _ Hbf (proj2 (Hics cs eq_refl)) (Hbex _ Hrefs)).
            - (* the components at the top of the bound: class types, and references of a lower rank *)
              pose proof (wf_bounds_ranked env wf p) as Hrk. rewrite <- Hg in Hrk. cbn [to_generic ranked_below] in Hrk.
              change (forallb (ranked_below env (parameter_rank env p)) (map to_generic cs) = true) in Hrk.
              rewrite forallb_forall in Hrk.
              intros c Hc'. pose proof (Hrk c Hc') as Hrc. apply in_map_iff in Hc'. destruct Hc' as [C [<- HC]].
              pose proof (proj1 (Hics cs eq_refl) C HC) as HCf.
              destruct (compfrag_cases env C HCf) as [Hif|[q [-> _]]].
              2:{ (* a narrowed type variable, of a lower rank *)
                  cbn [to_generic ranked_below rank_of param_of] in Hrc |- *. apply Nat.ltb_lt in Hrc.
                  pose proof (vars_in_intersected _ _ Hsv _ (in_map Nullable _ _ HC)) as HsvC. cbn [vars_in] in HsvC.
                  apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
                  destruct (Hps q HsvC) as [S' Hin'].
                  assert (HRq: R r (mkGenericRef None true q [])).
                  { exists q, S', None, true. split; [reflexivity|]. split; [exact Hin'|].
                    split; [unfold rank_of in Hrc; cbn [param_of] in Hrc; lia|right].
                    exact (HNp' p _ Hin (not_in_fragment _ Ens) (ifrag_inter (Nullable (Intersection cs)) cs eq_refl)). }
                  destruct (HRr _ HRq) as [Hbr _]. cbn [bound_in_top_h]. rewrite Hbr. cbn [andb no_type_variables variables_of].
                  exact (refs_top env wf b Kr' (R r) HRr (Hclose r) _ HRq). }
              destruct (ifrag_cases env wf C Hif) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]]; try reflexivity.
              cbn [to_generic ranked_below rank_of param_of] in Hrc |- *. apply Nat.ltb_lt in Hrc.
              pose proof (vars_in_intersected _ _ Hsv _ (in_map Nullable _ _ HC)) as HsvC. cbn [vars_in] in HsvC.
              apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
              destruct (Hps q HsvC) as [S' Hin'].
              assert (HRq: R r (mkGenericRef None false q []))
                  by (apply (Rplain r q S' Hin'); unfold rank_of in Hrc; cbn [param_of] in Hrc; lia).
              destruct (HRr _ HRq) as [Hbr _]. cbn [bound_in_top_h]. rewrite Hbr. cbn [andb no_type_variables variables_of].
              exact (refs_top env wf b Kr' (R r) HRr (Hclose r) _ HRq).
            - exact (in_fragment_without_null env _ HlF).
            - (* each component, made nullable, takes the lower bound: it takes that without null *)
              intros c Hc'. apply in_map_iff in Hc'. destruct Hc' as [C [<- HC]].
              destruct (Hc _ (in_map Nullable _ _ HC)) as [f Ef].
              pose proof (proj1 (Hics cs eq_refl) C HC) as HCf.
              destruct (compfrag_cases env C HCf) as [Hif|[q [-> _]]].
              2:{ (* a narrowed type variable: the type it is bound to, without null *)
                  pose proof (vars_in_intersected _ _ Hsv _ (in_map Nullable _ _ HC)) as HsvC. cbn [vars_in] in HsvC.
                  apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
                  destruct (Hps q HsvC) as [S' Hin']. destruct (Hval q S' Hin') as [o' [Hlq _]].
                  cbn [to_generic inst_nested param_of] in Ef |- *. rewrite Hlq in Ef |- *.
                  unfold inst_ref, inst_fit in Ef |- *. cbn [given_mutability is_narrowed] in Ef |- *.
                  exact (rewrap_takes f _ _ (in_fragment_without_null env _ (Hbf q o' _ Hlq)) HlF Ef). }
              assert (EN: forall m cl args, inst_nested env b (to_generic (Nullable (RootResolved m cl args)))
                  = Nullable (inst_nested env b (to_generic (RootResolved m cl args)))) by (intros; reflexivity).
              destruct (ifrag_cases env wf C Hif) as [[m [cl [args [-> _]]]]|[->|[[m [cl [args [-> _]]]]|[q [-> _]]]]].
              + rewrite EN in Ef. destruct f as [|f]; [discriminate Ef|]. exists f. rewrite (unify_nullable_target env f _ _ [] HlF) in Ef. exact Ef.
              + unfold bottom_type in Ef |- *. rewrite EN in Ef.
                destruct f as [|f]; [discriminate Ef|]. exists f. rewrite (unify_nullable_target env f _ _ [] HlF) in Ef. exact Ef.
              + (* not nullable, as a component *)
                destruct (Hshape _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
                apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. discriminate Hsh.
              + (* a type variable: the type it is bound to *)
                pose proof (vars_in_intersected _ _ Hsv _ (in_map Nullable _ _ HC)) as HsvC. cbn [vars_in] in HsvC.
                apply andb_true_iff in HsvC. destruct HsvC as [HsvC _]. apply andb_true_iff in HsvC. destruct HsvC as [_ HsvC].
                destruct (Hps q HsvC) as [S' Hin']. destruct (Hval q S' Hin') as [o' [Hlq _]].
                cbn [to_generic inst_nested param_of] in Ef |- *. rewrite Hlq in Ef |- *.
                unfold inst_ref, inst_fit in Ef |- *. cbn [given_mutability is_narrowed] in Ef |- *.
                exact (rewrap_takes f _ _ (Hbf q o' _ Hlq) HlF Ef). }
          destruct Hi as [f Hf]. exists (S f).
          change (inst_nested env b (Nullable (Intersection (map to_generic cs))))
              with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
          exact (unify_rewrap_target env _ _ _ [] _ HlF Hf). }
      destruct (uniform_fuel_list vars (fun f v => parameter_rank env (fst v) < S r ->
          unify env f (inst_nested env b (parameter_bound env (fst v))) (value_of b (fst v)) (Ongoing []) = Some (Ongoing [])))
          as [K HK].
      { intros f f' v Hle E Hr. exact (unify_fuel_monotone env f f' _ _ _ _ Hle (E Hr)). }
      { intros [p S] Hin. cbn [fst]. destruct (Nat.eq_dec (parameter_rank env p) r) as [Heq|Hne].
        - destruct (Hp p S Hin Heq) as [f Ef]. exists f. intros _. exact Ef.
        - exists Kr. intros Hr. apply (IHr p S Hin). lia. }
      exists K. intros p S Hin Hr. exact (HK (p, S) Hin Hr). }
    destruct (Hwithin rmax) as [K0 HK0]. destruct (HR rmax K0 HK0) as [K [HK0K HRm]].
    split; [exact Hsat|]. exists K.
    split; [intros p S Hin; exact (unify_fuel_monotone env K0 K _ _ _ _ HK0K (HK0 p S Hin (Hrmax p S Hin)))|].
    (* the types that mention only the type parameters of vars are bound in b *)
    intros P Hpf Hpl Hv Ho.
    assert (Hplain: exists P', no_generics P' = true /\ vars_in (fun q => existsb (param_eqb q) ps) P' = true
        /\ owners_in (fun q => existsb (param_eqb q) ps) P' = true /\ (args_plain P' = true \/ Np = true)
        /\ bound_in env b K [] (pgeneric P) = bound_in env b K [] (to_generic P')).
    { destruct (pfrag_cases env P Hpf) as [Hif|[[gm [nn [q [-> _]]]]|[gm [nn [q [-> _]]]]]].
      - exists P. rewrite (pgeneric_ifrag env wf P Hif). split; [exact (ifrag_no_generics env P Hif)|]. split; [exact Hv|].
        split; [exact Ho|]. split; [destruct Hpl as [E|E]; [left; exact E|right; exact (HNpx E)]|reflexivity].
      (* a type variable of a mutability given to it, narrowed or made nullable: the plain reference *)
      - exists (TypeVariable (mkGenericRef None false q [])). split; [reflexivity|]. split; [exact Hv|]. split; [reflexivity|].
        split; [left; reflexivity|reflexivity].
      - exists (TypeVariable (mkGenericRef None false q [])). split; [reflexivity|]. split; [exact Hv|]. split; [reflexivity|].
        split; [left; reflexivity|reflexivity]. }
    destruct Hplain as [P' [Hng [Hv' [Ho' [Hpl' ->]]]]].
    apply (refs_bound_in env wf b K (R rmax) HRm (Hclose rmax)).
    destruct Hpl' as [Hpl'|EN].
    - apply (refs_of_vars (fun q => existsb (param_eqb q) ps) (R rmax) b P' Hng Hv' Ho' Hpl').
      + intros q E. destruct (Hps q E) as [S Hin]. exact (Rplain rmax q S Hin (Hrmax q S Hin)).
      + exact Hown.
    - apply (refs_of_vars_any (fun q => existsb (param_eqb q) ps) (R rmax) b P' Hng Hv' Ho').
      + intros gm nn q E. destruct (Hps q E) as [S Hin]. exists q, S, gm, nn. split; [reflexivity|]. split; [exact Hin|].
        split; [exact (Hrmax q S Hin)|right; exact EN].
      + exact Hown.
Qed.

(*
 * An invocation of a function whose type parameters are bounded by types mentioning them, inferred,
 * is sound: where unify accepts each argument for its parameter, in turn, and inference picks a lower
 * bound for each variable whose bound has type variables (for an F-bounded one, Kotlin reports that
 * it can't infer it otherwise), the final values are within the declared bounds, instantiated with
 * them, and each argument fits its parameter with the type variables replaced by them. Where a bound
 * is neither a class type nor a type of the parameters (ifrag): an intersection, or a type variable of
 * a mutability given to it, narrowed or made nullable (`T : U?`), that takes the final values to be
 * class types.
 *)
Theorem invocation_with_bounded_variables_sound: forall n vars Ps As U,
    NoDup (map fst vars) ->
    (forall p S, In (p, S) vars -> static_bound vars p S) ->
    (forall P, In P Ps -> pfrag env P = true /\ vars_in (fun q => existsb (param_eqb q) (map fst vars)) P = true
        /\ owners_in (fun q => existsb (param_eqb q) (map fst vars)) P = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (for_inference_of vars []) = Some (Ongoing U) ->
    (forall p S st, In (p, S) vars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    (forall p S, In (p, S) vars -> bfrag (final_of U p) -> xfrag (final_of U p)) ->
    ((exists P, In P Ps /\ args_plain P = false)
        \/ (exists p S, In (p, S) vars /\ in_fragment env S = false /\ (ifrag env S = false \/ args_plain S = false)) ->
        forall p S, In (p, S) vars -> in_fragment env (final_of U p) = true) ->
    forall b, b = map (fun v => (fst v, TypeArgument invariant ref (final_of U (fst v)))) vars ->
    (exists K, forall p S, In (p, S) vars ->
        unify env K (inst_nested env b (parameter_bound env p)) (final_of U p) (Ongoing []) = Some (Ongoing []))
    /\ forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n vars Ps As U Hnd Hst HPs HAs Hfold Hlow Hfinal Hclass b Hbdef.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) []))) vars).
    assert (Hs0: for_inference_of vars [] = Ongoing s0) by reflexivity. rewrite Hs0 in Hfold.
    assert (Hl0: forall p S, In (p, S) vars -> lookup_state s0 p = Some (mkVariableState S (initial_upper_bound S) bottom_type false false)).
    { intros p S Hin. exact (lookup_for_inference vars [] p S Hnd Hin). }
    (* the variable states inference starts with *)
    assert (Hwf0: wf_states env xfrag bfrag s0).
    { intros p st Hp. destruct (lookup_for_inference_in vars [] p st Hp) as [S Hin].
      rewrite (Hl0 p S Hin) in Hp. injection Hp as <-. exact (static_initial_ok vars p S (Hst p S Hin) s0). }
    destruct (invocation_sound env wf xfrag bfrag types supertype_of_classes n Ps As s0 U Hwf0 (fun P HP => proj1 (HPs P HP)) HAs Hfold)
        as [HwfU Hsound].
    destruct (fold_keeps_exact_unify env n _ s0 U Hfold) as [_ [Hkeep2 _]].
    (* the bindings: the final values *)
    assert (Hlb: forall p S, In (p, S) vars -> lookup_binding b p = Some (TypeArgument invariant ref (final_of U p))).
    { intros p S Hin. rewrite Hbdef. exact (lookup_map_vars vars (fun v => TypeArgument invariant ref (final_of U (fst v))) p S Hnd Hin). }
    assert (Hlb_in: forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars /\ a = TypeArgument invariant ref (final_of U q)).
    { intros q a Eq. rewrite Hbdef in Eq. destruct (lookup_own vars (fun q => TypeArgument invariant ref (final_of U q)) q a Eq) as [Ea Hq].
      apply in_map_iff in Hq. destruct Hq as [[q1 S] [Hfst Hin]]. simpl in Hfst. subst q1. exists S. split; [exact Hin|exact Ea]. }
    assert (Hvar: forall p S, In (p, S) vars -> binds_var U b p S).
    { intros p S Hin. destruct (Hkeep2 p _ (Hl0 p S Hin) eq_refl eq_refl) as [st [Hl [He [_ Hs]]]].
      assert (Ef: final_of U p = final_value env st) by (unfold final_of; rewrite Hl; reflexivity).
      assert (Hx: xfrag (final_of U p)).
      { apply (Hfinal p S Hin). rewrite Ef. destruct (HwfU p st Hl) as [_ [_ [Hw _]]]. destruct (Hw He) as [_ [_ [Hbu [Hbl _]]]].
        unfold final_value. destruct (is_non_nullable_nothing env (lower_bound st)); assumption. }
      exists ref, (final_of U p), st. split; [exact (Hlb p S Hin)|]. split; [reflexivity|]. split; [exact Hx|].
      split; [exact Hl|]. split; [rewrite Ef in Hx |- *; exact (final_value_fits env xfrag bfrag types U p st ref HwfU Hl He Hx)|].
      rewrite He. split; [exact Hs|]. intros Ens. pose proof (Hlow p S st Hin Ens Hl) as Hnn.
      split; [rewrite Ef; unfold final_value; rewrite Hnn; reflexivity|exact Hnn]. }
    assert (Hdom: forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars).
    { intros q a Eq. destruct (Hlb_in q a Eq) as [S [Hin _]]. exists S. exact Hin. }
    set (extra := existsb (fun P => negb (args_plain P)) Ps).
    assert (Hextra: extra = true -> exists P, In P Ps /\ args_plain P = false).
    { intros E. apply existsb_exists in E. destruct E as [P [HP EP]]. exists P. split; [exact HP|].
      destruct (args_plain P); [discriminate EP|reflexivity]. }
    assert (Hplain: forall P, In P Ps -> args_plain P = true \/ extra = true).
    { intros P HP. destruct (args_plain P) eqn:EP; [left; reflexivity|right].
      apply existsb_exists. exists P. split; [exact HP|]. rewrite EP. reflexivity. }
    assert (Hbf: (extra = true \/ exists p S, In (p, S) vars /\ in_fragment env S = false /\ (ifrag env S = false \/ args_plain S = false)) ->
        bindings_in_fragment env b).
    { intros Hex q o x Eq. destruct (Hlb_in q _ Eq) as [S' [Hin' Ea]]. injection Ea as -> ->. refine (Hclass _ q S' Hin').
      destruct Hex as [E|E]; [left; exact (Hextra E)|right; exact E]. }
    destruct (bindings_within vars U b extra Hst HwfU Hdom Hvar Hbf) as [Hsat [K [HK Hb]]].
    split.
    - exists K. intros p S Hin. pose proof (HK p S Hin) as E.
      unfold value_of in E. rewrite (Hlb p S Hin) in E. exact E.
    - intros P A Hin. apply (Hsound b K); [|exact Hsat|exact Hin].
      intros P' HP. destruct (HPs P' HP) as [Hif [Hv Ho]]. exact (Hb P' Hif (Hplain P' HP) Hv Ho).
Qed.

(*
 * Calling a member function whose type parameters are bounded by types mentioning them is sound, too,
 * the type parameters of the class among those (`class Box<E> { fn m<T : Comparable<in E>>(...) }`).
 * The receiver captures the type arguments of the class, whose type parameters are bounded by class
 * types; the object called on is of a class e below that of the receiver, its type arguments exact,
 * and as those of c within the bounds. Where unify accepts each argument for its parameter, in turn,
 * and inference picks a lower bound for each variable of the function whose bound has type variables,
 * the final values are within the declared bounds, instantiated with them and with the type arguments
 * of the object, and each argument fits its parameter with the type parameters replaced by those.
 * Where a bound is neither a class type nor a type of the parameters, that takes the final values to
 * be class types.
 *)
Theorem member_call_with_bounded_variables_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p S, In (p, S) (cvars ++ ovars) -> static_bound (cvars ++ ovars) p S) ->
    (forall p S, In (p, S) cvars -> in_fragment env S = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is; its type arguments are exact, and as those of c within the bounds *)
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> pfrag env P = true /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true
        /\ owners_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    (forall p S, In (p, S) ovars -> bfrag (final_of U p) -> xfrag (final_of U p)) ->
    ((exists P, In P Ps /\ args_plain P = false)
        \/ (exists p S, In (p, S) ovars /\ in_fragment env S = false /\ (ifrag env S = false \/ args_plain S = false)) ->
        forall p S, In (p, S) ovars -> in_fragment env (final_of U p) = true) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument invariant ref (final_of U (fst v)))) ovars ->
    (exists K, forall p S, In (p, S) ovars ->
        unify env K (inst_nested env b (parameter_bound env p)) (final_of U p) (Ongoing []) = Some (Ongoing []))
    /\ forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hst Hcb Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HAs Hfold Hlow Hfinal Hclass b Hbdef.
    pose proof (object_arguments_exact env wf c mo e xs zs He (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) Hfo Hxx Hzs)
        as Hzx.
    destruct (receiver_and_object_with env wf xfrag bfrag n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hcb
        (fun p S Hin => static_initial_ok (cvars ++ ovars) p S (Hst p S (in_or_app _ _ _ (or_intror Hin)))) Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu [Hp _]]]]]]]]].
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    destruct (invocation_sound env wf xfrag bfrag types supertype_of_classes nf Ps As u U Hwfu (fun P HP => proj1 (HPs P HP)) HAs Hfold)
        as [HwfU Hsound].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep [Hkeep2 _]].
    assert (Hndo: NoDup (map fst ovars)).
    { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
      inversion H. apply IH. assumption. }
    (* the bindings: the type arguments of the object as c, and the final values of the function's *)
    assert (HlbC: forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z -> lookup_binding b p = Some z).
    { intros i p S z Hi Hz. assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
      rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz). reflexivity. }
    assert (HlbO: forall p S, In (p, S) ovars -> lookup_binding b p = Some (TypeArgument invariant ref (final_of U p))).
    { intros p S Hin.
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
      exact (lookup_map_vars ovars (fun v => TypeArgument invariant ref (final_of U (fst v))) p S Hndo Hin). }
    assert (Hdom: forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars).
    { intros p a Hpb. rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a'|] eqn:Ec.
      - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
      - destruct (lookup_own ovars (fun q => TypeArgument invariant ref (final_of U q)) p _ Hpb) as [_ Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        exists bound. apply in_or_app. right. exact Hin. }
    (* how each type parameter is bound *)
    assert (Hvar: forall p S, In (p, S) vars -> binds_var U b p S).
    { intros p S Hin. unfold vars in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - (* of c: the type argument of the object, captured by that of the receiver *)
        destruct (In_nth_error _ _ Hin) as [i Hi].
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        destruct (Hzb i p S z Hi Hz) as [o [x [f [Ez Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. rewrite Ez in Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hfx].
        exists o, x, (mkVariableState S y y true true). split; [rewrite <- Ez; exact (HlbC i p S z Hi Hz)|].
        split; [exact Ho|]. split; [exact (it_in_fragment_xfrag env xfrag bfrag types _ Hfx)|].
        split; [exact (Hkeep p _ (Hcap i p S y Hi Hy) eq_refl)|].
        split.
        + pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy2.
          destruct y as [| | | |vb ob X| |]; try discriminate Hfy2.
          unfold fits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n1. split; [reflexivity|]. split; [reflexivity|].
          split; [exact Hfy2|]. split; [exact Hfx|]. apply (unify_fuel_monotone env n1); [lia|].
          pose proof (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy) as E. rewrite Ez in E. exact E.
        + cbn [is_exact]. split; [exact (in_fragment_no_vars env _ (Hcb p S Hin))|]. exists f. exact Ef.
      - (* of the function: its final value *)
        destruct (Hkeep2 p _ (Hownu p S Hin) eq_refl eq_refl) as [st [HlU [He' [_ Hs]]]].
        assert (Ef: final_of U p = final_value env st) by (unfold final_of; rewrite HlU; reflexivity).
        assert (Hx: xfrag (final_of U p)).
        { apply (Hfinal p S Hin). rewrite Ef. destruct (HwfU p st HlU) as [_ [_ [Hw _]]]. destruct (Hw He') as [_ [_ [Hbu [Hbl _]]]].
          unfold final_value. destruct (is_non_nullable_nothing env (lower_bound st)); assumption. }
        exists ref, (final_of U p), st. split; [exact (HlbO p S Hin)|]. split; [reflexivity|]. split; [exact Hx|].
        split; [exact HlU|]. split; [rewrite Ef in Hx |- *; exact (final_value_fits env xfrag bfrag types U p st ref HwfU HlU He' Hx)|].
        rewrite He'. split; [exact Hs|]. intros Ens. pose proof (Hlow p S st Hin Ens HlU) as Hnn.
        split; [rewrite Ef; unfold final_value; rewrite Hnn; reflexivity|exact Hnn]. }
    (* where a bound of the function is neither a class type nor a type of the parameters, the bindings are class types *)
    set (extra := existsb (fun P => negb (args_plain P)) Ps).
    assert (Hextra: extra = true -> exists P, In P Ps /\ args_plain P = false).
    { intros E. apply existsb_exists in E. destruct E as [P [HP EP]]. exists P. split; [exact HP|].
      destruct (args_plain P); [discriminate EP|reflexivity]. }
    assert (Hplain: forall P, In P Ps -> args_plain P = true \/ extra = true).
    { intros P HP. destruct (args_plain P) eqn:EP; [left; reflexivity|right].
      apply existsb_exists. exists P. split; [exact HP|]. rewrite EP. reflexivity. }
    assert (Hbf: (extra = true \/ exists p S, In (p, S) vars /\ in_fragment env S = false /\ (ifrag env S = false \/ args_plain S = false)) ->
        bindings_in_fragment env b).
    { intros Hpre q o x Eq. destruct (Hdom q _ Eq) as [S Hin]. unfold vars in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (HlbC i q S z Hi Hz) in Eq. injection Eq as ->.
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. exact (proj2 Hex).
      - rewrite (HlbO q S Hin) in Eq. injection Eq as _ <-. refine (Hclass _ q S Hin).
        destruct Hpre as [E|[p0 [S0 [Hin0 [Ens0 Ei0]]]]]; [left; exact (Hextra E)|right].
        unfold vars in Hin0. apply in_app_or in Hin0. destruct Hin0 as [Hin0|Hin0].
        { rewrite (Hcb p0 _ Hin0) in Ens0. discriminate Ens0. }
        exists p0, S0. exact (conj Hin0 (conj Ens0 Ei0)). }
    destruct (bindings_within vars U b extra Hst HwfU Hdom Hvar Hbf) as [Hsat [K [HK Hb]]].
    split.
    - exists K. intros p S Hin. pose proof (HK p S (in_or_app _ _ _ (or_intror Hin))) as E.
      unfold value_of in E. rewrite (HlbO p S Hin) in E. exact E.
    - intros P A Hin. apply (Hsound b K); [|exact Hsat|exact Hin].
      intros P' HP. destruct (HPs P' HP) as [Hif [Hv Ho]]. exact (Hb P' Hif (Hplain P' HP) Hv Ho).
Qed.


End Invocation.

End FBounded.

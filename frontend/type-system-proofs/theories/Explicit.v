From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
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
From EmergeTypeSystem Require Import FBounded.
From Stdlib Require Import Bool List Arith Lia Sorting.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Explicit type arguments for functions whose bounds mention type variables                      *)
(*                                                                                                *)
(* TypeUnification.fromExplicit binds the type parameters of a function exactly to the explicit    *)
(* type arguments, in the order they are declared (Subtyping.bind_explicit): each is checked       *)
(* against the upper bound and, where its static upper bound mentions type variables, against that *)
(* with the type argument in place of the variable (plus_static_check), the variables of a lower   *)
(* rank bound already. The type arguments are within the declared bounds, instantiated with them,   *)
(* and the arguments of the call fit the parameters so instantiated                                *)
(* (explicit_invocation_with_bounded_variables_sound).                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Section Explicit.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* What binding a variable exactly to an explicit type argument does: the type is checked against the
   upper bound and, where the static upper bound has type variables, against that with the type in place
   of the variable; then the variable is bound *)
Lemma explicit_step: forall n p S s o x u,
    lookup_state s p = Some (mkVariableState S (initial_upper_bound S) bottom_type false false) ->
    in_fragment env x = true ->
    plus_exact_binding env (unify env n) s p (TypeArgument invariant o x) = Some (Ongoing u) ->
    exists s2, u = set_state s2 p (mkVariableState S (TypeArgument invariant o x) (TypeArgument invariant o x) true false)
        /\ (exists w, unify env n (initial_upper_bound S) x (Ongoing s) = Some (Ongoing w))
        /\ (if no_vars S then s2 = s else unify env n (with_candidate env p x S) x (Ongoing s) = Some (Ongoing s2)).
Proof.
    intros n p S s o x u Hl Hx H. unfold plus_exact_binding in H. rewrite Hl in H.
    cbn [upper_bound lower_bound static_upper_bound is_capturable] in H.
    destruct (unify env n (initial_upper_bound S) x (Ongoing s)) as [[w|]|] eqn:E1; try discriminate H.
    destruct (unify env n (TypeArgument invariant o x) bottom_type (Ongoing s)) as [[w'|]|] eqn:E2; try discriminate H.
    assert (Ew: w' = s).
    { destruct n as [|n]; [discriminate E2|].
      rewrite unify_step_once in E2. unfold unify_step, unify_type_argument in E2. cbn beta iota zeta in E2.
      change (unify env n x bottom_type (Ongoing s) = Some (Ongoing w')) in E2.
      exact (proj1 (keeps_states_with_arguments env wf n) x bottom_type s w' Hx (bottom_in_fragment env wf) E2). }
    subst w'. unfold plus_binding_check, plus_static_check in H. cbn [static_upper_bound] in H.
    destruct (no_vars S) eqn:Ens.
    - injection H as <-. exists s. split; [reflexivity|]. split; [exists w; reflexivity|reflexivity].
    - destruct (unify env n (with_candidate env p x S) x (Ongoing s)) as [[s2|]|] eqn:E3; try discriminate H.
      injection H as <-. exists s2. split; [reflexivity|]. split; [exists w; reflexivity|reflexivity].
Qed.

Variables xfrag bfrag: EType -> Prop.
Hypothesis types: inference_types env xfrag bfrag.
Hypothesis supertype_of_classes: closest_common_supertype_of_classes env.
Let wf_states := Constraints.wf_states env xfrag bfrag.
Let satisfies := Constraints.satisfies env xfrag.

Definition initial_state (S: EType): VariableState := mkVariableState S (initial_upper_bound S) bottom_type false false.
Definition exact_state (S t: EType): VariableState := mkVariableState S t t true false.

(* An explicit type argument: exact, of a class type *)
Definition explicit_argument (t: EType): Prop :=
    exists o x, t = TypeArgument invariant o x /\ is_exact_ownership o = true /\ afrag env x = true /\ closed x = true.

(* The variables of vars, as binding them to the explicit type arguments ts leaves them: each as it starts,
   or bound exactly to its type argument *)
Definition explicit_states (vars: list (TypeParameterId * EType)) (ts: list EType) (s: VariableStates): Prop :=
    (forall q st, lookup_state s q = Some st -> exists i S t, nth_error vars i = Some (q, S) /\ nth_error ts i = Some t
        /\ (st = initial_state S \/ st = exact_state S t))
    /\ forall i q S, nth_error vars i = Some (q, S) -> exists st, lookup_state s q = Some st.

(* Those are the variable states unify works with *)
Lemma explicit_wf: forall vars ts s, (forall p S, In (p, S) vars -> static_bound env bfrag vars p S) ->
    (forall t, In t ts -> explicit_argument t) -> explicit_states vars ts s -> wf_states s.
Proof.
    intros vars ts s Hst Hts [Hex _] q st Hq. destruct (Hex q st Hq) as [i [S [t [Hi [Ht [-> | ->]]]]]].
    - exact (static_initial_ok env wf xfrag bfrag types vars q S (Hst q S (nth_error_In _ _ Hi)) s).
    - destruct (Hts t (nth_error_In _ _ Ht)) as [o [x [-> [_ [Hx _]]]]].
      pose proof (Inference.in_fragment_no_vars env x (afrag_in_fragment env x Hx)) as Hnx.
      unfold exact_state. cbn [upper_bound lower_bound is_exact static_upper_bound].
      split; [exact Hnx|]. split; [exact Hnx|]. split; [intros E; discriminate E|].
      destruct (Hst q S (nth_error_In _ _ Hi)) as [_ [_ [Hsv _]]].
      exact (vars_in_mono _ _ (fun r E => proj1 (proj1 (andb_true_iff _ _) E)) _ Hsv).
Qed.

(* The explicit type arguments satisfy them, each below the upper bound it is checked against *)
Lemma explicit_satisfies: forall vars ts s, NoDup (map fst vars) ->
    (forall t, In t ts -> explicit_argument t) -> explicit_states vars ts s ->
    (forall i p S o x, nth_error vars i = Some (p, S) -> nth_error ts i = Some (TypeArgument invariant o x) ->
        exists f, unify env f (initial_upper_bound S) x (Ongoing []) = Some (Ongoing [])) ->
    satisfies (combine (map fst vars) ts) s.
Proof.
    intros vars ts s Hnd Hts [Hex Hdom] Hup q o x Eq.
    destruct (lookup_combine_nth _ _ q _ Eq) as [i [Hi Ht]].
    rewrite nth_error_map in Hi. destruct (nth_error vars i) as [[q' S]|] eqn:Hv; [|discriminate Hi].
    injection Hi as ->.
    destruct (Hts _ (nth_error_In _ _ Ht)) as [o' [x' [Et [Ho [Hx Hc]]]]]. injection Et as <- <-.
    pose proof (afrag_in_fragment env x Hx) as HxF.
    split; [exact (it_in_fragment_xfrag env xfrag bfrag types x HxF)|].
    destruct (Hdom i q S Hv) as [st Hst]. exists st. split; [exact Hst|].
    destruct (Hex q st Hst) as [j [S' [t [Hj [Htj Est]]]]].
    assert (Eij: j = i).
    { apply (proj1 (NoDup_nth_error _) Hnd j i).
      - rewrite length_map. apply nth_error_Some. rewrite Hj. discriminate.
      - rewrite !nth_error_map, Hj, Hv. reflexivity. }
    subst j. rewrite Hv in Hj. injection Hj as <-. rewrite Ht in Htj. injection Htj as <-.
    destruct Est as [-> | ->].
    - unfold fits, initial_state. cbn [is_exact lower_bound upper_bound].
      split; [exists 2; exact (below_all env wf [] x 2 HxF (le_n _) _)|exact (Hup i q S o x Hv Ht)].
    - unfold fits, exact_state. cbn [is_exact lower_bound upper_bound].
      exists invariant, o, x, (argument_depth (TypeArgument invariant o x)).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact HxF|].
      apply (proj2 (reflexivity_with_arguments env _)); [|lia]. exact HxF.
Qed.

Lemma bind_explicit_failed: forall f ps args, bind_explicit env f ps args Failed = Some Failed.
Proof. intros f [|p ps] [|a args]; reflexivity. Qed.

Lemma initial_no_vars: forall S, no_vars (initial_upper_bound S) = true.
Proof. intros S. unfold initial_upper_bound. destruct (no_vars S) eqn:E; [exact E|reflexivity]. Qed.

Lemma sorted_app_r: forall (R: TypeParameterId -> TypeParameterId -> Prop) l1 l2, StronglySorted R (l1 ++ l2) -> StronglySorted R l2.
Proof. intros R l1 l2. induction l1 as [|a l1 IH]; intros H; [exact H|]. inversion H. exact (IH H2). Qed.

(* The facts of the check of a type argument x for the variable p against its static upper bound S,
   whatever bindings satisfy the variable states s0 *)
Definition checked_at (s0: VariableStates) (p: TypeParameterId) (S x: EType): Prop :=
    forall C, In C (intersected_components S) -> forall b K,
        bound_in env b K [] (to_generic (with_candidate env p x C)) = true -> satisfies b s0 ->
        ((exists cs, inter_of S = Some cs) -> bindings_in_fragment env b) ->
        exists f, unify env f (inst env b (with_candidate env p x C)) x (Ongoing []) = Some (Ongoing []).

(* Binding the variables to the explicit type arguments in turn: each bound exactly, below the upper
   bound and checked against the static upper bound *)
Lemma explicit_arguments: forall n vars ts pre tpre rest trest s u,
    vars = pre ++ rest -> ts = tpre ++ trest -> length tpre = length pre -> length trest = length rest ->
    NoDup (map fst vars) -> StronglySorted (fun p q => parameter_rank env p < parameter_rank env q) (map fst vars) ->
    (forall p S, In (p, S) vars -> static_bound env bfrag vars p S) ->
    (forall t, In t ts -> explicit_argument t) ->
    explicit_states vars ts s ->
    (forall p S, In (p, S) rest -> lookup_state s p = Some (initial_state S)) ->
    (forall q st, lookup_state s q = Some st -> is_exact st = false -> In q (map fst rest)) ->
    bind_explicit env (unify env n) (map fst rest) trest (Ongoing s) = Some (Ongoing u) ->
    explicit_states vars ts u
    /\ (forall q st, lookup_state u q = Some st -> is_exact st = true)
    /\ (forall q, ~ In q (map fst rest) -> lookup_state u q = lookup_state s q)
    /\ (forall i p S t, nth_error rest i = Some (p, S) -> nth_error trest i = Some t ->
        lookup_state u p = Some (exact_state S t)
        /\ forall o x, t = TypeArgument invariant o x ->
            (exists f, unify env f (initial_upper_bound S) x (Ongoing []) = Some (Ongoing []))
            /\ (no_vars S = false -> exists s0, explicit_states vars ts s0 /\ checked_at s0 p S x)).
Proof.
    intros n vars ts pre tpre rest. revert pre tpre. induction rest as [|[p S] rest IH];
        intros pre tpre [|t trest] s u Ev Et Hlp Hlr Hnd Hsort Hst Hts Hs Hinit Hne H; simpl in Hlr; try discriminate Hlr.
    - simpl in H. injection H as <-. split; [exact Hs|]. split.
      { intros q st Hq. destruct (is_exact st) eqn:E; [reflexivity|]. destruct (Hne q st Hq E). }
      split; [reflexivity|]. intros [|i]; discriminate.
    - assert (Hin: In (p, S) vars) by (rewrite Ev; apply in_or_app; right; left; reflexivity).
      assert (Hint: In t ts) by (rewrite Et; apply in_or_app; right; left; reflexivity).
      destruct (Hts t Hint) as [o [x [-> [Ho [Hx Hcx]]]]].
      pose proof (afrag_in_fragment env x Hx) as HxF.
      pose proof (Inference.in_fragment_no_vars env x HxF) as Hnx.
      simpl in H. destruct (plus_exact_binding env (unify env n) s p (TypeArgument invariant o x)) as [[u1|]|] eqn:E;
          [|rewrite bind_explicit_failed in H; discriminate H|discriminate H].
      pose proof (Hinit p S (or_introl eq_refl)) as Hlp0.
      destruct (explicit_step n p S s o x u1 Hlp0 HxF E) as [s2 [Eu1 [[w Ew] Hchk]]].
      pose proof (explicit_wf vars ts s Hst Hts Hs) as Hwf.
      destruct (Hst p S Hin) as [Hg [Hcomp [Hsv [Hcl [Hics _]]]]].
      assert (Hsv': vars_in (static_vars env p) S = true)
          by exact (vars_in_mono _ _ (fun r E => proj1 (proj1 (andb_true_iff _ _) E)) _ Hsv).
      (* the variables of a lower rank: bound already *)
      assert (Hrest: forall q, In q (map fst rest) -> parameter_rank env p < parameter_rank env q).
      { rewrite Ev, map_app in Hsort. pose proof (sorted_app_r _ _ _ Hsort) as Hs'. cbn [map fst] in Hs'.
        inversion Hs' as [|? ? _ Hhead]. rewrite Forall_forall in Hhead. exact Hhead. }
      assert (Hpnr: ~ In p (map fst rest)).
      { rewrite Ev, map_app in Hnd. apply NoDup_app_remove_l in Hnd. cbn [map fst] in Hnd. inversion Hnd. assumption. }
      (* the check leaves the variable states as they are *)
      assert (Hsame: same_states s2 s).
      { destruct (no_vars S) eqn:Ens; [rewrite Hchk; intros q; reflexivity|].
        apply (check_same env wf (it_intersect_no_vars env xfrag bfrag types) (it_supertype_no_vars env xfrag bfrag types)
            n p x S s s2 (wf_ranked env xfrag bfrag s Hwf) Hsv' Hnx); [|exact Hchk].
        intros q st Hq Hr. destruct (is_exact st) eqn:Ex; [reflexivity|].
        destruct (Hne q st Hq Ex) as [Eq|Hq']; [cbn [fst] in Eq; subst q; lia|]. pose proof (Hrest q Hq'). lia. }
      assert (Hlu1: forall q, q <> p -> lookup_state u1 q = lookup_state s q)
          by (intros q Hq; rewrite Eu1, lookup_set_other by (intros ->; exact (Hq eq_refl)); exact (Hsame q)).
      assert (Hpu1: lookup_state u1 p = Some (exact_state S (TypeArgument invariant o x))) by (rewrite Eu1; apply lookup_set_same).
      destruct (IH (pre ++ [(p, S)]) (tpre ++ [TypeArgument invariant o x]) trest u1 u
          ltac:(rewrite Ev, <- app_assoc; reflexivity) ltac:(rewrite Et, <- app_assoc; reflexivity)
          ltac:(rewrite !length_app; cbn; lia) ltac:(lia) Hnd Hsort Hst Hts) as [Hsu [Hexu [Hothu Hidx]]].
      + (* the variable states after binding p *)
        destruct Hs as [Hex Hdom]. split.
        * intros q st Hq. destruct (Nat.eq_dec p q) as [<-|Hne'].
          -- rewrite Hpu1 in Hq. injection Hq as <-. exists (length pre), S, (TypeArgument invariant o x).
             split; [rewrite Ev, nth_error_app2, Nat.sub_diag by lia; reflexivity|].
             split; [rewrite Et, nth_error_app2, <- Hlp, Nat.sub_diag by lia; reflexivity|right; reflexivity].
          -- rewrite (Hlu1 q (fun E => Hne' (eq_sym E))) in Hq. exact (Hex q st Hq).
        * intros i q S' Hi. destruct (Nat.eq_dec p q) as [<-|Hne']; [exists (exact_state S (TypeArgument invariant o x)); exact Hpu1|].
          rewrite (Hlu1 q (fun E => Hne' (eq_sym E))). exact (Hdom i q S' Hi).
      + intros q S' Hq. assert (Hqp: q <> p) by (intros ->; apply Hpnr; exact (in_map fst _ _ Hq)).
        rewrite (Hlu1 q Hqp). exact (Hinit q S' (or_intror Hq)).
      + intros q st Hq Ex. destruct (Nat.eq_dec p q) as [<-|Hne'].
        * rewrite Hpu1 in Hq. injection Hq as <-. discriminate Ex.
        * rewrite (Hlu1 q (fun E => Hne' (eq_sym E))) in Hq.
          destruct (Hne q st Hq Ex) as [Eq|Hq']; [cbn [fst] in Eq; contradiction|exact Hq'].
      + exact H.
      + split; [exact Hsu|]. split; [exact Hexu|]. split.
        { intros q Hq. cbn [map fst In] in Hq. rewrite (Hothu q (fun H' => Hq (or_intror H'))).
          apply Hlu1. intros ->. apply Hq. left. reflexivity. }
        intros [|i] q S' t' Hi Ht'.
        * cbn in Hi, Ht'. injection Hi as <- <-. injection Ht' as <-.
          split; [rewrite (Hothu p Hpnr); exact Hpu1|].
          intros o' x' Ex'. injection Ex' as <- <-. split.
          { exists n. destruct (keeps_free env wf n _ x s w
                (initial_no_vars S) Hnx Ew) as [_ E0].
            exact E0. }
          intros Ens. rewrite Ens in Hchk. exists s. split; [exact Hs|].
          assert (Hform: static_form env p S).
          { destruct (static_initial_ok env wf xfrag bfrag types vars p S (Hst p S Hin) s) as [_ [_ [Hexo _]]].
            destruct (Hexo eq_refl) as [_ [_ [_ [_ Hok]]]]. unfold Constraints.static_ok in Hok.
            cbn [static_upper_bound] in Hok. rewrite Ens in Hok. destruct Hok as [_ [_ [_ [_ [Hform _]]]]]. exact Hform. }
          destruct (static_whole env wf xfrag bfrag types n p S x s s2
              (proj1 (constraints_with_arguments env wf xfrag bfrag types supertype_of_classes n))
              (fun j _ => leaf_all env wf xfrag bfrag types supertype_of_classes j
                  (proj1 (constraints_with_arguments env wf xfrag bfrag types supertype_of_classes j)))
              (fun C HC => proj1 (Hcomp C HC)) Hform Hx Hcx Hwf Hchk) as [_ [_ Hall]].
          intros C HC b K Hb Hsb Hbf. apply (Hall C HC b K Hb); [|exact Hbf].
          intros q o' x' Eq. destruct (Hsb q o' x' Eq) as [Hx' [st [Hq Hfit]]]. split; [exact Hx'|].
          exists st. split; [rewrite (Hsame q); exact Hq|exact Hfit].
        * exact (Hidx i q S' t' Hi Ht').
Qed.

Lemma lookup_combine_index: forall (ids: list TypeParameterId) (xs: list EType) i p x, NoDup ids ->
    nth_error ids i = Some p -> nth_error xs i = Some x -> lookup_binding (combine ids xs) p = Some x.
Proof.
    induction ids as [|q ids IH]; intros [|y xs] [|i] p x Hnd Hi Hx; simpl in Hi, Hx; try discriminate.
    - injection Hi as ->. injection Hx as ->. simpl. rewrite param_eqb_refl. reflexivity.
    - inversion Hnd as [|? ? Hnot Hnd']. subst. simpl. destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnot. exact (nth_error_In _ _ Hi).
      + exact (IH xs i p x Hnd' Hi Hx).
Qed.

(*
 * An invocation of a function whose type parameters are bounded by types mentioning them, with an
 * explicit type argument for each, of a class type, is sound: where binding them to the type arguments
 * in turn succeeds, each checked against its bound, and unify accepts each argument for its parameter,
 * the type arguments are within the declared bounds, instantiated with them, and each argument fits
 * its parameter with the type parameters replaced by them. The type parameters are declared in order:
 * a bound mentions those declared before.
 *)
Theorem explicit_invocation_with_bounded_variables_sound: forall n vars ts s Ps As nf U,
    NoDup (map fst vars) ->
    StronglySorted (fun p q => parameter_rank env p < parameter_rank env q) (map fst vars) ->
    (forall p S, In (p, S) vars -> static_bound env bfrag vars p S) ->
    (* the explicit type arguments, bound in turn *)
    length ts = length vars -> (forall t, In t ts -> explicit_argument t) ->
    bind_explicit env (unify env n) (map fst vars) ts (for_inference_of vars []) = Some (Ongoing s) ->
    (* the parameters and the arguments, accepted in turn *)
    (forall P, In P Ps -> qfrag env P = true /\ vars_in (fun q => existsb (param_eqb q) (map fst vars)) P = true
        /\ forall C, In C (intersected_components P) -> owners_in (fun q => existsb (param_eqb q) (map fst vars)) C = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing s) = Some (Ongoing U) ->
    forall b, b = combine (map fst vars) ts ->
    (exists K, forall p S, In (p, S) vars ->
        unify env K (inst_nested env b (parameter_bound env p)) (value_of b p) (Ongoing []) = Some (Ongoing []))
    /\ forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n vars ts s Ps As nf U Hnd Hsort Hst Hl Hts Hbind HPs HAs Hfold b Hbdef.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) []))) vars).
    assert (Hs0: for_inference_of vars [] = Ongoing s0) by reflexivity. rewrite Hs0 in Hbind.
    assert (Hl0: forall p S, In (p, S) vars -> lookup_state s0 p = Some (initial_state S))
        by (intros p S Hin; exact (lookup_for_inference vars [] p S Hnd Hin)).
    (* the variable states inference starts with: each as it starts *)
    assert (Hes0: explicit_states vars ts s0).
    { split.
      - intros q st Hq. destruct (lookup_for_inference_in vars [] q st Hq) as [S Hin].
        rewrite (Hl0 q S Hin) in Hq. injection Hq as <-. destruct (In_nth_error _ _ Hin) as [i Hi].
        destruct (nth_error_same_length vars ts i _ (eq_sym Hl) Hi) as [t Ht].
        exists i, S, t. split; [exact Hi|]. split; [exact Ht|left; reflexivity].
      - intros i q S Hi. exists (initial_state S). exact (Hl0 q S (nth_error_In _ _ Hi)). }
    assert (Hne0: forall q st, lookup_state s0 q = Some st -> is_exact st = false -> In q (map fst vars)).
    { intros q st Hq _. destruct (lookup_for_inference_in vars [] q st Hq) as [S Hin]. exact (in_map fst _ _ Hin). }
    destruct (explicit_arguments n vars ts [] [] vars ts s0 s eq_refl eq_refl eq_refl Hl Hnd Hsort Hst Hts Hes0
        (fun p S Hin => Hl0 p S Hin) Hne0 Hbind) as [Hes [Hexs [_ Hidx]]].
    pose proof (explicit_wf vars ts s Hst Hts Hes) as Hwf.
    destruct (invocation_sound env wf xfrag bfrag types supertype_of_classes nf Ps As s U Hwf (fun P HP => proj1 (HPs P HP)) HAs Hfold)
        as [HwfU Hsound].
    destruct (fold_keeps_exact_unify env nf _ s U Hfold) as [Hkeep _].
    (* the bindings: the explicit type arguments, class types *)
    assert (Hlb: forall i p S t, nth_error vars i = Some (p, S) -> nth_error ts i = Some t -> lookup_binding b p = Some t).
    { intros i p S t Hi Ht. rewrite Hbdef. apply (lookup_combine_index _ ts i p t Hnd); [|exact Ht].
      rewrite nth_error_map, Hi. reflexivity. }
    assert (Hdom: forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars).
    { intros q a Eq. rewrite Hbdef in Eq. destruct (lookup_combine_nth _ ts q a Eq) as [i [Hi _]].
      rewrite nth_error_map in Hi. destruct (nth_error vars i) as [[q' S]|] eqn:Hv; [|discriminate Hi].
      injection Hi as ->. exists S. exact (nth_error_In _ _ Hv). }
    assert (Hbfin: bindings_in_fragment env b).
    { intros q o x Eq. rewrite Hbdef in Eq. destruct (lookup_combine_nth _ ts q _ Eq) as [i [_ Ht]].
      destruct (Hts _ (nth_error_In _ _ Ht)) as [o' [x' [Et [_ [Hx _]]]]]. injection Et as _ ->.
      exact (afrag_in_fragment env x' Hx). }
    (* how each type parameter is bound: exactly, to a type argument within its bound or checked against it *)
    assert (Hvar: forall p S, In (p, S) vars -> binds_var env xfrag U b p S).
    { intros p S Hin. destruct (In_nth_error _ _ Hin) as [i Hi].
      destruct (nth_error_same_length vars ts i _ (eq_sym Hl) Hi) as [t Ht].
      destruct (Hidx i p S t Hi Ht) as [Hps Hfacts].
      destruct (Hts t (nth_error_In _ _ Ht)) as [o [x [-> [Ho [Hx Hcx]]]]].
      pose proof (afrag_in_fragment env x Hx) as HxF.
      destruct (Hfacts o x eq_refl) as [[f Ef] Hchecked].
      exists o, x, (exact_state S (TypeArgument invariant o x)).
      split; [exact (Hlb i p S _ Hi Ht)|]. split; [exact Ho|].
      split; [exact (it_in_fragment_xfrag env xfrag bfrag types x HxF)|].
      split; [exact (Hkeep p _ Hps eq_refl)|].
      split.
      { unfold fits, exact_state. cbn [is_exact lower_bound upper_bound].
        exists invariant, o, x, (argument_depth (TypeArgument invariant o x)).
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HxF|]. split; [exact HxF|].
        apply (proj2 (reflexivity_with_arguments env _)); [|lia]. exact HxF. }
      unfold exact_state. cbn [is_exact]. right.
      destruct (no_vars S) eqn:Ens.
      - left. split; [reflexivity|]. exists f. rewrite (initial_closed S Ens) in Ef. exact Ef.
      - right. split; [reflexivity|].
        destruct (Hchecked eq_refl) as [s1 [Hes1 Hchk]].
        assert (Hform: static_form env p S).
        { destruct (static_initial_ok env wf xfrag bfrag types vars p S (Hst p S Hin) s) as [_ [_ [Hexo _]]].
          destruct (Hexo eq_refl) as [_ [_ [_ [_ Hok]]]]. unfold Constraints.static_ok in Hok.
          cbn [static_upper_bound] in Hok. rewrite Ens in Hok. destruct Hok as [_ [_ [_ [_ [Hform _]]]]]. exact Hform. }
        (* the type arguments satisfy the states the check was made at *)
        assert (Hsb1: satisfies b s1).
        { rewrite Hbdef. apply (explicit_satisfies vars ts s1 Hnd Hts Hes1).
          intros j q S' o' x' Hj Htj. destruct (Hidx j q S' _ Hj Htj) as [_ Hf']. destruct (Hf' o' x' eq_refl) as [Hup _]. exact Hup. }
        split; [exact Hx|]. split; [exact Hcx|]. split; [exact Hform|].
        intros C HC K Hb _ Hbf. exact (Hchk C HC b K Hb Hsb1 Hbf). }
    destruct (bindings_within env wf xfrag bfrag types vars U b true Hst HwfU Hdom Hvar (fun _ => Hbfin))
        as [Hsat [K [HK Hb]]].
    split.
    - exists K. exact HK.
    - intros P A Hin. apply (Hsound b K); [|exact Hsat| |exact Hin].
      + intros P' HP. destruct (HPs P' HP) as [Hif [Hv Ho]]. exact (Hb P' Hif (or_intror eq_refl) (fun _ => eq_refl) Hv Ho).
      + intros _. exact Hbfin.
Qed.

End Explicit.

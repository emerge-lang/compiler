From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Unify and the variable states                                                                   *)
(*                                                                                                *)
(* On types without type variables, unify neither changes the variable states nor depends on them  *)
(* (unify_free); and a type variable bound exactly stays so, with the same binding                 *)
(* (unify_keeps_exact). Constraints.v builds on both.                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Definition relabel (s': VariableStates) (r: Unification): Unification :=
    match r with Ongoing _ => Ongoing s' | Failed => Failed end.

Section Variables.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.

Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Lemma no_vars_of_components: forall cs, (forall c, In c cs -> no_vars c = true) -> no_vars (of_components env cs) = true.
Proof.
    intros cs H. assert (Hi: forallb no_vars (map (fun c => with_mutability env
            (fold_left intersect_mutability (map (assignment_mutability env) cs) readonly) (without_null env c)) cs) = true).
    { apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      apply no_vars_set_mutability. rewrite no_vars_without_null. exact (H c' Hc'). }
    assert (Hk: forallb no_vars (map (with_mutability env
            (fold_left intersect_mutability (map (assignment_mutability env) cs) readonly)) cs) = true).
    { apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      apply no_vars_set_mutability. exact (H c' Hc'). }
    destruct cs as [|c [|c' cs']]; [reflexivity|exact (H c (or_introl eq_refl))|].
    unfold of_components. destruct (negb (forallb (is_nullable env) _)); [exact Hi|].
    destruct (forallb is_nullable_type _); [exact Hi|exact Hk].
Qed.

Lemma no_vars_intersected: forall t, no_vars t = true -> forall c, In c (intersected_components t) -> no_vars c = true.
Proof.
    intros t H c Hc. destruct t as [| [] | | | | |cs]; simpl in Hc;
        try (destruct Hc as [<-|[]]; exact H).
    - apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']]. simpl in H |- *. rewrite forallb_forall in H. exact (H c' Hc').
    - simpl in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.

Lemma no_vars_final_argument: forall a, no_vars a = true -> no_vars (final_argument a) = true.
Proof. intros [| | | |v o x| |] H; try exact H. unfold final_argument. destruct (_ || _); exact H. Qed.

Lemma no_vars_instantiate_h: forall U b t, (forall g, variables_of g = [] -> no_vars (U g) = true) ->
    (forall p a, lookup_binding b p = Some a -> no_vars a = true) ->
    no_vars t = true -> no_vars (instantiate_h env U b t) = true.
Proof.
    intros U b t HU Hb. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; simpl in H; try discriminate H.
    - simpl. apply forallb_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as [a' [<- Ha']].
      rewrite forallb_forall in H.
      apply (IH (esize a')); [pose proof (esize_in args a' Ha'); simpl; lia|reflexivity|apply H, Ha'].
    - simpl. rewrite no_vars_rewrap. apply (IH (esize n)); simpl; auto.
    - destruct vs; [|discriminate H]. simpl.
      assert (Hf: no_vars (match lookup_binding b p with Some a => final_argument a | None => U (mkGenericRef gm nn p []) end) = true).
      { destruct (lookup_binding b p) eqn:E; [exact (no_vars_final_argument e (Hb p e E))|apply HU; reflexivity]. }
      destruct nn; [rewrite no_vars_without_null|]; (destruct gm; [apply no_vars_set_mutability|]; exact Hf).
    - reflexivity.
    - simpl. assert (Hn: no_vars (instantiate_h env U b n) = true) by (apply (IH (esize n)); simpl; auto).
      destruct (instantiate_h env U b n) as [mi ci ai|ni|gi|mei msgi|vi oi ni|gi|csi] eqn:E;
          cbn beta iota zeta;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
          simpl in Hn |- *; rewrite ?no_vars_rewrap; simpl in Hn |- *;
          try reflexivity; try exact Hn; try (rewrite ?andb_true_r; exact Hn).
    - simpl. rewrite forallb_forall in H.
      assert (Hcs: forall c', In c' cs -> no_vars (instantiate_h env U b c') = true)
          by (intros c' Hc'; apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc']).
      destruct (intersect_instances_cases env (map (instantiate_h env U b) cs)) as [l' [Hl' [E|[v E]]]]; rewrite E; cbn [no_vars];
          apply no_vars_of_components; intros c Hc; apply in_flat_map in Hc; destruct Hc as [i [Hi Hc]];
          refine (no_vars_intersected i _ c Hc);
          destruct (Hl' i Hi) as [Hi'|[v' [o' Hi']]]; apply in_map_iff in Hi'; destruct Hi' as [c' [Ec Hc']];
          pose proof (Hcs c' Hc') as Hn; rewrite Ec in Hn; exact Hn.
Qed.

(* An unbound type parameter becomes its effective bound, instantiated, the type parameters without
   a binding in it, too, down to the level of its rank *)
Lemma no_vars_instantiate: forall b t, (forall p a, lookup_binding b p = Some a -> no_vars a = true) ->
    no_vars t = true -> no_vars (instantiate env b t) = true.
Proof.
    intros b t Hb H. rewrite instantiate_top. apply no_vars_instantiate_h; [|exact Hb|exact H].
    intros g Hg. unfold instantiate_unbound, through. generalize (S (rank_of env g)) as k. intros k. revert g Hg.
    induction k as [|k IHk]; intros g Hg; [reflexivity|]. cbn [through_level].
    apply no_vars_instantiate_h; [exact IHk|exact Hb|].
    destruct g as [gm nn p vs]. cbn [variables_of] in Hg. subst vs. rewrite (effective_bound_eq env ranked).
    cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
    pose proof (wf_bounds_mention_no_variables env wf p) as Hd.
    destruct nn; [rewrite no_vars_without_null|]; (destruct gm; [apply no_vars_set_mutability|]; exact Hd).
Qed.

Lemma lookup_combine_in: forall (ids: list TypeParameterId) (xs: list EType) p a,
    lookup_binding (combine ids xs) p = Some a -> In a xs.
Proof.
    intros ids. induction ids as [|q ids IH]; intros [|x xs] p a H; simpl in H; try discriminate H.
    destruct (param_eqb p q); [injection H as <-; left; reflexivity|right; exact (IH xs p a H)].
Qed.

Lemma normalized_no_vars: forall ca aargs ct, forallb no_vars aargs = true ->
    forall a, In a (parameterized_supertype_arguments env ca aargs ct) -> no_vars a = true.
Proof.
    intros ca aargs ct Haargs a Ha. unfold parameterized_supertype_arguments in Ha.
    pose proof (supertypes_mention_no_variables ca ct) as Hs. unfold supertype_arguments in Hs.
    destruct (parameterized_supertype env ca ct) as [m c sargs| | | | | |]; try destruct Ha.
    apply in_map_iff in Ha. destruct Ha as [r [<- Hr]]. apply no_vars_instantiate; [|exact (Hs r Hr)].
    intros p a' Ha'. rewrite forallb_forall in Haargs. apply Haargs. exact (lookup_combine_in _ _ p a' Ha').
Qed.

Lemma no_vars_filter: forall cs, forallb no_vars cs = true ->
    filter is_type_variable cs = [] /\ filter (fun c => negb (is_type_variable c)) cs = cs.
Proof.
    induction cs as [|c cs IH]; intros H; [split; reflexivity|]. simpl in H. apply andb_true_iff in H. destruct H as [Hc H].
    destruct (IH H) as [IH1 IH2]. destruct c as [| | | | |[]|]; simpl in Hc |- *; try discriminate Hc; rewrite IH1, IH2; split; reflexivity.
Qed.

Lemma capturable_no_vars: forall t s, no_vars t = true -> capturable t s = None.
Proof. intros [| | | | |[]|] s H; simpl in H; try discriminate H; reflexivity. Qed.

Section StateFree.

Variable f: UnifyFn.
Hypothesis Hf: forall t a s s' r, no_vars t = true -> no_vars a = true ->
    f t a (Ongoing s) = Some r -> f t a (Ongoing s') = Some (relabel s' r).
Hypothesis Hff: forall t a, f t a Failed = Some Failed.

Lemma fold_failed: forall {A: Type} (h: Unification -> A -> option Unification) (l: list A),
    (forall x, In x l -> h Failed x = Some Failed) -> fold_unify h l Failed = Some Failed.
Proof.
    intros A h l Hh. induction l as [|x l IH]; [reflexivity|]. simpl. rewrite (Hh x (or_introl eq_refl)).
    apply IH. intros y Hy. apply Hh. right. exact Hy.
Qed.

Lemma fold_free: forall {A: Type} (h: Unification -> A -> option Unification) (l: list A) s s' r,
    (forall x, In x l -> forall s0 s0' r0, h (Ongoing s0) x = Some r0 -> h (Ongoing s0') x = Some (relabel s0' r0)) ->
    (forall x, In x l -> h Failed x = Some Failed) ->
    fold_unify h l (Ongoing s) = Some r -> fold_unify h l (Ongoing s') = Some (relabel s' r).
Proof.
    intros A h l. induction l as [|x l IH]; intros s s' r Hh Hfail H; simpl in *.
    - injection H as <-. reflexivity.
    - destruct (h (Ongoing s) x) as [[w|]|] eqn:E; try discriminate H.
      + rewrite (Hh x (or_introl eq_refl) s s' _ E). simpl.
        exact (IH w s' r (fun y Hy => Hh y (or_intror Hy)) (fun y Hy => Hfail y (or_intror Hy)) H).
      + rewrite (Hh x (or_introl eq_refl) s s' _ E). simpl.
        rewrite (fold_failed h l (fun y Hy => Hfail y (or_intror Hy))) in H |- *. injection H as <-. reflexivity.
Qed.

Lemma find_first_free: forall (h: VariableStates -> EType -> option Unification) (l: list EType) s s' res,
    (forall x, In x l -> forall s0 s0' r0, h s0 x = Some r0 -> h s0' x = Some (relabel s0' r0)) ->
    find_first (h s) l = Some res ->
    find_first (h s') l = Some (match res with Some (c, _) => Some (c, s') | None => None end).
Proof.
    intros h l. induction l as [|x l IH]; intros s s' res Hh H; simpl in *.
    - injection H as <-. reflexivity.
    - destruct (h s x) as [[w|]|] eqn:E; try discriminate H.
      + rewrite (Hh x (or_introl eq_refl) s s' _ E). injection H as <-. reflexivity.
      + rewrite (Hh x (or_introl eq_refl) s s' _ E). exact (IH s s' res (fun y Hy => Hh y (or_intror Hy)) H).
Qed.

Lemma flipped_free: forall target cs s s' r, no_vars target = true -> forallb no_vars cs = true ->
    intersection_flipped_unify f target cs s = Some r -> intersection_flipped_unify f target cs s' = Some (relabel s' r).
Proof.
    intros target cs s s' r Ht Hcs H. unfold intersection_flipped_unify in *. rewrite forallb_forall in Hcs.
    destruct (find_first (fun c => f target c (Ongoing s)) cs) as [res|] eqn:E; [|discriminate H].
    rewrite (find_first_free (fun st c => f target c (Ongoing st)) cs s s' res
        (fun x Hx s0 s0' r0 E0 => Hf target x s0 s0' r0 Ht (Hcs x Hx) E0) E).
    destruct res as [[c w]|]; injection H as <-; reflexivity.
Qed.

Lemma pairs_free: forall targs aargs s s' r, forallb no_vars targs = true -> forallb no_vars aargs = true ->
    unify_arguments f targs aargs s = Some r -> unify_arguments f targs aargs s' = Some (relabel s' r).
Proof.
    intros targs aargs s s' r Ht Ha H. unfold unify_arguments in *. rewrite forallb_forall in Ht, Ha.
    apply (fold_free _ _ s s' r); [| |exact H].
    - intros [t a] Hin s0 s0' r0 E. apply in_combine_l in Hin as Hl. apply in_combine_r in Hin as Hr.
      exact (Hf t a s0 s0' r0 (Ht t Hl) (Ha a Hr) E).
    - intros [t a] _. apply Hff.
Qed.

Ltac nv := first
    [ assumption | reflexivity
    | match goal with |- no_vars (read_type ?v ?t) = true => destruct v; first [assumption|reflexivity] end
    | simpl; assumption
    | rewrite no_vars_without_null; simpl; assumption
    | apply (no_vars_effective_bound env wf); simpl; assumption ].

Ltac free H := match type of H with f ?x ?y (Ongoing _) = Some ?r => exact (Hf x y _ _ r ltac:(nv) ltac:(nv) H) end.

Ltac inter a H Ht Hv Hnv tcs s s' :=
    cbn zeta in H |- *; rewrite Hv, Hnv in H |- *; rewrite forallb_forall in Ht;
    destruct (fold_unify (fun inner c => f c a inner) tcs (Ongoing s)) as [c2|] eqn:E1; [|discriminate H];
    rewrite (fold_free (fun inner c => f c a inner) tcs s s' c2
        (fun x Hx s1 s1' r0 E0 => Hf x a s1 s1' r0 (Ht x Hx) ltac:(nv) E0) (fun x _ => Hff x a) E1);
    destruct c2 as [s2|]; unfold relabel at 1; cbn beta iota in H |- *; [|injection H as <-; reflexivity];
    destruct (find_first (fun c => f c a (Ongoing s2)) tcs) as [cov|] eqn:E2; [|discriminate H];
    let E3 := fresh "E3" in
    pose proof (find_first_free (fun st c => f c a (Ongoing st)) tcs s2 s' cov
        (fun y Hy s1 s1' r0 E0 => Hf y a s1 s1' r0 (Ht y Hy) ltac:(nv) E0) E2) as E3;
    cbn beta in E3; rewrite E3;
    destruct cov as [[c w]|]; cbn beta iota in H |- *; injection H as <-; reflexivity.

Lemma unify_step_free: forall t a s s' r, no_vars t = true -> no_vars a = true ->
    unify_step env f t a s = Some r -> unify_step env f t a s' = Some (relabel s' r).
Proof.
    intros t a s s' r Ht Ha H.
    destruct t as [mt ct targs|tn|[gt nnt pt bt]|mte msgt|vt ot tt|[gt nnt pt bt]|tcs]; simpl in Ht; try discriminate Ht;
        unfold unify_step in H |- *.
    - (* a class type *)
      unfold unify_root_resolved in H |- *.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha.
      + destruct (negb (base_type_is_subtype_of env ca ct)); [injection H as <-; reflexivity|].
        destruct (negb (Model.is_subtype_of _ _)); [injection H as <-; reflexivity|].
        destruct (class_eqb ca nothing); [injection H as <-; reflexivity|].
        apply (pairs_free _ _ s s' r Ht); [|exact H].
        destruct (class_eqb ca ct); [exact Ha|]. apply forallb_forall. apply normalized_no_vars. exact Ha.
      + injection H as <-. reflexivity.
      + free H.
      + free H.
      + free H.
      + (eapply flipped_free; [|exact Ha|exact H]; nv).
    - (* a nullable type *)
      unfold unify_nullable in H |- *.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try free H.
    - (* a type parameter *)
      unfold unify_generic in H |- *.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try free H.
      + destruct (is_non_nullable_nothing env _ && _); injection H as <-; reflexivity.
      + injection H as <-. reflexivity.
      + destruct (param_eqb pa _); [|free H].
        match type of H with context [if ?c then _ else _] => destruct c end; injection H as <-; reflexivity.
      + (eapply flipped_free; [|exact Ha|exact H]; nv).
    - (* an erroneous type *)
      unfold unify_erroneous in H |- *.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha; free H.
    - (* a type argument *)
      unfold unify_type_argument in H |- *.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha;
          cbn beta iota zeta in H |- *;
          try (destruct (Variance_beq vt output); cbn [negb andb] in H |- *;
               [destruct (is_non_nullable_nothing env _); injection H as <-; reflexivity|]);
          try free H; try (eapply flipped_free; [|exact Ha|exact H]; nv).
      destruct (ownership_is_assignable_to oa ot); [|injection H as <-; reflexivity].
      rewrite (capturable_no_vars tt s Ht) in H. rewrite (capturable_no_vars tt s' Ht).
      destruct vt, va; simpl in H |- *; try (injection H as <-; reflexivity); try free H.
      destruct (f tt ta (Ongoing s)) as [[w|]|] eqn:E; try discriminate H.
      + rewrite (Hf tt ta s s' _ Ht Ha E). simpl in H |- *. free H.
      + rewrite (Hf tt ta s s' _ Ht Ha E). simpl in H |- *. rewrite Hff in H |- *. injection H as <-. reflexivity.
    - (* an intersection *)
      unfold unify_intersection, intersection_body in H |- *.
      destruct (no_vars_filter tcs Ht) as [Hv Hnv].
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try (destruct (negb (is_nullable env _)); [injection H as <-; reflexivity|]; inter (Nullable an) H Ht Hv Hnv tcs s s');
          try free H.
      + inter (RootResolved ma ca aargs) H Ht Hv Hnv tcs s s'.
      + inter (Generic (mkGenericRef ga nna pa ba)) H Ht Hv Hnv tcs s s'.
      + inter (TypeArgument va oa ta) H Ht Hv Hnv tcs s s'.
      + inter (Intersection acs) H Ht Hv Hnv tcs s s'.
Qed.


End StateFree.

(* unify on types without type variables neither changes the variable states nor depends on them *)
Lemma unify_free: forall n t a s s' r, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some r -> unify env n t a (Ongoing s') = Some (relabel s' r).
Proof.
    induction n as [|n IH]; intros t a s s' r Ht Ha H; [discriminate H|].
    rewrite unify_step_once in H |- *.
    exact (unify_step_free (unify env n) IH (unify_keeps_failure env n) t a s s' r Ht Ha H).
Qed.

End Variables.

(* ---------------------------------------------------------------------------------------------- *)
(* A type variable bound exactly stays so                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* Variables bound exactly stay bound so, to the same; those that aren't, and can't be captured,
   stay so, too; and no variable is added (TypeUnification sets the states of variables it looks up
   only) *)
Definition keeps_exact (s s': VariableStates): Prop :=
    (forall p st, lookup_state s p = Some st -> is_exact st = true -> lookup_state s' p = Some st)
    /\ (forall p st, lookup_state s p = Some st -> is_exact st = false -> is_capturable st = false ->
        exists st', lookup_state s' p = Some st' /\ is_exact st' = false /\ is_capturable st' = false
            /\ static_upper_bound st' = static_upper_bound st)
    /\ (forall p, lookup_state s p = None -> lookup_state s' p = None).

Lemma keeps_exact_refl: forall s, keeps_exact s s.
Proof. intros s. split; [intros p st H _; exact H|]. split; [|intros p H; exact H]. intros p st H He Hc. exists st. auto. Qed.

Lemma keeps_exact_trans: forall s1 s2 s3, keeps_exact s1 s2 -> keeps_exact s2 s3 -> keeps_exact s1 s3.
Proof.
    intros s1 s2 s3 [H1 [H1' H1n]] [H2 [H2' H2n]]. split; [intros p st Hl He; exact (H2 p st (H1 p st Hl He) He)|].
    split; [|intros p Hn; exact (H2n p (H1n p Hn))].
    intros p st Hl He Hc. destruct (H1' p st Hl He Hc) as [st' [Hl' [He' [Hc' Hs']]]].
    destruct (H2' p st' Hl' He' Hc') as [st'' [Hl'' [He'' [Hc'' Hs'']]]]. exists st''. rewrite Hs'' in *. auto.
Qed.

(* A variable with a state after a unification had one before *)
Lemma keeps_exact_domain: forall s s' p st', keeps_exact s s' -> lookup_state s' p = Some st' -> exists st, lookup_state s p = Some st.
Proof.
    intros s s' p st' [_ [_ Hn]] Hl'. destruct (lookup_state s p) as [st|] eqn:Hl; [exists st; reflexivity|].
    rewrite (Hn p Hl) in Hl'. discriminate Hl'.
Qed.

Lemma keeps_exact_set: forall s s' p st st', lookup_state s p = Some st -> is_exact st = false ->
    (is_capturable st = false -> is_exact st' = false /\ is_capturable st' = false
        /\ static_upper_bound st' = static_upper_bound st) ->
    keeps_exact s s' -> keeps_exact s (set_state s' p st').
Proof.
    intros s s' p st st' Hl He Hst [H [H' Hn]]. split; [|split].
    - intros q stq Hq Heq. destruct (Nat.eq_dec p q) as [<-|Hne].
      + rewrite Hl in Hq. injection Hq as <-. rewrite He in Heq. discriminate Heq.
      + rewrite lookup_set_other by exact Hne. exact (H q stq Hq Heq).
    - intros q stq Hq Heq Hcq. destruct (Nat.eq_dec p q) as [<-|Hne].
      + rewrite Hl in Hq. injection Hq as <-. exists st'. rewrite lookup_set_same. destruct (Hst Hcq). auto.
      + rewrite lookup_set_other by exact Hne. exact (H' q stq Hq Heq Hcq).
    - intros q Hq. destruct (Nat.eq_dec p q) as [<-|Hne]; [rewrite Hl in Hq; discriminate Hq|].
      rewrite lookup_set_other by exact Hne. exact (Hn q Hq).
Qed.

Section KeepsExact.

Variable env: Environment.
Variable f: UnifyFn.
Hypothesis Hf: forall t a s s', f t a (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Hypothesis Hff: forall t a, f t a Failed = Some Failed.

Lemma fold_keeps_exact: forall {A: Type} (h: Unification -> A -> option Unification) (l: list A) s s',
    (forall x s0 s0', In x l -> h (Ongoing s0) x = Some (Ongoing s0') -> keeps_exact s0 s0') ->
    (forall x, In x l -> h Failed x = Some Failed) ->
    fold_unify h l (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros A h l. induction l as [|x l IH]; intros s s' Hh Hfail H; simpl in H.
    - injection H as <-. apply keeps_exact_refl.
    - destruct (h (Ongoing s) x) as [[w|]|] eqn:E; try discriminate H.
      + apply (keeps_exact_trans s w s'); [exact (Hh x s w (or_introl eq_refl) E)|].
        exact (IH w s' (fun y s0 s0' Hy => Hh y s0 s0' (or_intror Hy)) (fun y Hy => Hfail y (or_intror Hy)) H).
      + rewrite (fold_failed h l (fun y Hy => Hfail y (or_intror Hy))) in H. discriminate H.
Qed.

Lemma find_first_keeps_exact: forall (h: EType -> option Unification) (l: list EType) s c s',
    (forall x s0, h x = Some (Ongoing s0) -> keeps_exact s s0) ->
    find_first h l = Some (Some (c, s')) -> keeps_exact s s'.
Proof.
    intros h l. induction l as [|x l IH]; intros s c s' Hh H; simpl in H; [discriminate H|].
    destruct (h x) as [[w|]|] eqn:E; try discriminate H.
    - injection H as <- <-. exact (Hh x w E).
    - exact (IH s c s' Hh H).
Qed.

Lemma plus_subtype_keeps_exact: forall s p t s',
    plus_subtype_constraint env f s p t = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros s p t s' H. unfold plus_subtype_constraint in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (is_exact st) eqn:He; [exact (Hf _ _ _ _ H)|]. cbn zeta in H.
    destruct (is_non_nullable_nothing env _); [discriminate H|].
    destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E; cbn beta iota in H; try discriminate H. injection H as <-.
    refine (keeps_exact_set s w p st _ Hl He _ (Hf _ _ _ _ E)). intros Hc. split; [reflexivity|split; [exact Hc|reflexivity]].
Qed.

Lemma static_check_keeps_exact: forall st p c s s', plus_static_check env f st p c (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros st p c s s' H. unfold plus_static_check in H. destruct (no_vars _); [injection H as <-; apply keeps_exact_refl|].
    exact (Hf _ _ _ _ H).
Qed.

Lemma binding_check_keeps_exact: forall st p t s s', plus_binding_check env f st p t (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros st p t s s' H. unfold plus_binding_check in H.
    destruct t as [| | | |[] o x| |]; try (injection H as <-; apply keeps_exact_refl). exact (static_check_keeps_exact _ _ _ _ _ H).
Qed.

Lemma plus_supertype_keeps_exact: forall s p t s',
    plus_supertype_constraint env f s p t = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros s p t s' H. unfold plus_supertype_constraint in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (is_exact st) eqn:He; [exact (Hf _ _ _ _ H)|]. cbn zeta in H.
    destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E; cbn beta iota in H; try discriminate H.
    destruct (plus_static_check env f st p _ (Ongoing w)) as [[w2|]|] eqn:E2; cbn beta iota in H; try discriminate H. injection H as <-.
    refine (keeps_exact_set s w2 p st _ Hl He _ (keeps_exact_trans _ _ _ (Hf _ _ _ _ E) (static_check_keeps_exact _ _ _ _ _ E2))).
    intros Hc. split; [reflexivity|split; [exact Hc|reflexivity]].
Qed.

Lemma plus_exact_keeps_exact: forall s p t s',
    (forall st, lookup_state s p = Some st -> is_exact st = false /\ is_capturable st = true) ->
    plus_exact_binding env f s p t = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros s p t s' Hp H. unfold plus_exact_binding in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (Hp st eq_refl) as [He Hcap].
    cbn zeta in H. destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E1; cbn beta iota in H; try discriminate H.
    destruct (f t (lower_bound st) (Ongoing s)) as [[w'|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (plus_binding_check env f st p t (Ongoing w')) as [[w2|]|] eqn:E3; cbn beta iota in H; try discriminate H.
    injection H as <-.
    refine (keeps_exact_set s w2 p st _ Hl He _ (keeps_exact_trans _ _ _ (Hf _ _ _ _ E2) (binding_check_keeps_exact _ _ _ _ _ E3))).
    intros Hc. rewrite Hcap in Hc. discriminate Hc.
Qed.

Lemma flipped_keeps_exact: forall target cs s s',
    intersection_flipped_unify f target cs s = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros target cs s s' H. unfold intersection_flipped_unify in H.
    destruct (find_first (fun c => f target c (Ongoing s)) cs) as [[[c w]|]|] eqn:E; try discriminate H.
    injection H as <-. exact (find_first_keeps_exact _ cs s c w (fun x s0 E0 => Hf _ _ _ _ E0) E).
Qed.

Lemma capturable_some: forall t s p, capturable t s = Some p ->
    exists st, lookup_state s p = Some st /\ is_exact st = false /\ is_capturable st = true.
Proof.
    intros [| | | | |[gm nn q bnd]|] s p H; simpl in H; try discriminate H.
    destruct (lookup_state s q) as [st|] eqn:E; [|discriminate H].
    destruct (is_capturable st && negb (is_exact st)) eqn:Ec; [|discriminate H]. injection H as <-.
    exists st. split; [exact E|]. apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec].
    split; [destruct (is_exact st); [discriminate Ec|reflexivity]|exact Ec1].
Qed.

Lemma arguments_keep_exact: forall targs aargs s s', unify_arguments f targs aargs s = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros targs aargs s s' H. unfold unify_arguments in H. apply (fold_keeps_exact (fun inner '(target, assignee) => f target assignee inner) (combine targs aargs) s s'); [| |exact H].
    - intros [t a] s0 s0' _ E. exact (Hf t a s0 s0' E).
    - intros [t a] _. apply Hff.
Qed.

Ltac keeps H :=
    repeat match type of H with
    | Some (Ongoing _) = Some (Ongoing _) => injection H as <-; apply keeps_exact_refl
    | Some Failed = _ => discriminate H
    | None = _ => discriminate H
    | f _ _ (Ongoing _) = Some (Ongoing _) => exact (Hf _ _ _ _ H)
    | plus_subtype_constraint env f _ _ _ = _ => exact (plus_subtype_keeps_exact _ _ _ _ H)
    | plus_supertype_constraint env f _ _ _ = _ => exact (plus_supertype_keeps_exact _ _ _ _ H)
    | type_variable_flipped_unify env f _ _ _ = _ => exact (plus_subtype_keeps_exact _ _ _ _ H)
    | intersection_flipped_unify f _ _ _ = _ => exact (flipped_keeps_exact _ _ _ _ H)
    | unify_arguments f _ _ _ = _ => exact (arguments_keep_exact _ _ _ _ H)
    | context [if ?c then _ else _] => destruct c
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end.

Lemma unify_step_keeps_exact: forall t a s s', unify_step env f t a s = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros t a s s' H.
    destruct t as [mt ct targs|tn|[gt nnt pt bt]|mte msgt|vt ot tt|[gt nnt pt bt]|tcs]; unfold unify_step in H.
    - unfold unify_root_resolved in H. destruct a; cbn beta iota zeta in H; keeps H.
    - unfold unify_nullable in H. destruct a; cbn beta iota zeta in H; keeps H.
    - unfold unify_generic in H. destruct a; cbn beta iota zeta in H; keeps H.
    - unfold unify_erroneous in H. destruct a; cbn beta iota zeta in H; keeps H.
    - unfold unify_type_argument in H.
      destruct a as [| | |m msg|va oa ta| |]; cbn beta iota zeta in H;
          try (destruct (negb _ && _); [destruct (is_non_nullable_nothing env _); [injection H as <-; apply keeps_exact_refl|discriminate H]|]);
          try (keeps H; fail).
      destruct (ownership_is_assignable_to oa ot); cbn [negb] in H; [|discriminate H].
      destruct vt, va; cbn beta iota in H; try (keeps H; fail).
      all: destruct (capturable tt s) as [p|] eqn:Ec;
          [ destruct (capturable_some _ _ _ Ec) as [st0 [Hl0 [He0 Hc0]]];
            refine (plus_exact_keeps_exact s p _ _ _ H); intros st1 Hl1; rewrite Hl0 in Hl1; injection Hl1 as <-; auto
          | cbn beta iota in H ].
      all: try discriminate H.
      destruct (f tt ta (Ongoing s)) as [[w|]|] eqn:Ew; cbn beta iota in H; try discriminate H.
      + apply (keeps_exact_trans s w s'); [exact (Hf _ _ _ _ Ew)|exact (Hf _ _ _ _ H)].
      + rewrite Hff in H. discriminate H.
    - unfold unify_type_variable in H. destruct a; cbn beta iota zeta in H; keeps H.
    - unfold unify_intersection, intersection_body in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; cbn beta iota zeta in H;
          try (keeps H; fail).
      (* a nullable assignee, where the intersection may be null *)
      all: try (match type of H with (if ?c then _ else _) = _ => destruct c; [discriminate H|] end).
      all: match type of H with context [fold_unify ?h ?l (Ongoing ?q0)] =>
          destruct (fold_unify h l (Ongoing q0)) as [[s2|]|] eqn:E1; cbn beta iota in H; try discriminate H;
          assert (K1: keeps_exact s s2) by
              (apply (fold_keeps_exact h l s s2); [intros x y1 y2 _ E0; exact (Hf _ _ _ _ E0)|intros x _; apply Hff|exact E1])
          end.
      all: match type of H with context [find_first ?h ?l] =>
          destruct (find_first h l) as [[[c s3]|]|] eqn:E2; cbn beta iota in H; try discriminate H
          end.
      (* a type variable among the components, unified with Any, or with the assignee where that fails *)
      all: match type of H with fold_unify ?h ?l (Ongoing ?q3) = _ =>
          assert (K3: keeps_exact q3 s') by
              (apply (fold_keeps_exact h l q3 s');
               [ intros x y1 y2 _ E0; cbn beta in E0;
                 match type of E0 with context [match f ?t ?a ?c with _ => _ end] =>
                     destruct (f t a c) as [[?|]|] eqn:E3 in E0; cbn iota in E0;
                     [injection E0 as <-; exact (Hf _ _ _ _ E3)|first [discriminate E0|exact (Hf _ _ _ _ E0)]|discriminate E0]
                 end
               | intros x _; cbn beta; rewrite Hff; cbn iota; first [reflexivity|apply Hff]
               | exact H])
          end.
      all: try exact (keeps_exact_trans _ _ _ K1 K3).
      all: apply (keeps_exact_trans s s2 s'); [exact K1|]; apply (keeps_exact_trans s2 s3 s'); [|exact K3];
          exact (find_first_keeps_exact _ _ s2 c s3 (fun x y1 E0 => Hf _ _ _ _ E0) E2).
Qed.

End KeepsExact.

(* A type variable bound exactly stays so, with the same binding *)
Lemma unify_keeps_exact: forall env n t a s s', unify env n t a (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros env n. induction n as [|n IH]; intros t a s s' H; [discriminate H|].
    rewrite unify_step_once in H. exact (unify_step_keeps_exact env (unify env n) IH (unify_keeps_failure env n) t a s s' H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Unify touches type variables of a lower rank only                                               *)
(*                                                                                                *)
(* A candidate for the value of a variable is checked against its static upper bound, the        *)
(* variable itself replaced by the candidate (plus_static_check). The bound mentions variables of *)
(* a lower rank only, and so do theirs: the check leaves the states of the variable, and of those *)
(* of its rank or above, as they are (unify_keeps_from), which plus_supertype_constraint then     *)
(* sets.                                                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type variables of a type are among P; as in no_vars, references to type parameters have no
   type variables in their bounds *)
Fixpoint vars_in (P: TypeParameterId -> bool) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (vars_in P) arguments
    | Nullable n => vars_in P n
    | Generic (mkGenericRef _ _ _ vs) => match vs with [] => true | _ => false end
    | Error _ _ => true
    | TypeArgument _ _ n => vars_in P n
    | TypeVariable (mkGenericRef _ _ p vs) => P p && match vs with [] => true | _ => false end
    | Intersection components => forallb (vars_in P) components
    end.

Lemma no_vars_in: forall P t, no_vars t = true -> vars_in P t = true.
Proof.
    intros P. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] H; simpl in H |- *; try exact H; try discriminate H.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - exact (IH n H).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma vars_in_mono: forall (P P': TypeParameterId -> bool), (forall q, P q = true -> P' q = true) ->
    forall t, vars_in P t = true -> vars_in P' t = true.
Proof.
    intros P P' HP. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] H; simpl in H |- *; try exact H.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH a (proj1 H)), (IHa (proj2 H)). reflexivity.
    - exact (IH n H).
    - exact (IH n H).
    - apply andb_true_iff in H. rewrite (HP p (proj1 H)). exact (proj2 H).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H.
      rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma vars_in_rewrap: forall P t, vars_in P (rewrap_nullable t) = vars_in P t.
Proof. intros P [| | | | | |]; reflexivity. Qed.

Section VarsIn.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Lemma vars_in_without_null: forall P t, vars_in P (without_null env t) = vars_in P t.
Proof.
    intros P. fix IH 1. intros [m c a|n|[gm nn p b]|m msg|v o n|g|cs]; try reflexivity; simpl; [apply IH|apply IH|].
    destruct (forallb (is_nullable env) cs); [|reflexivity]. simpl.
    induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma vars_in_set_mutability: forall P m t, vars_in P t = true -> vars_in P (with_mutability env m t) = true.
Proof.
    intros P m t. remember (esize t) as k eqn:Hk. revert m t Hk. induction k as [k IH] using lt_wf_ind. intros m t -> H.
    destruct t as [mt c args|n|[gm nn p bnd]|me msg|v o n|[gm nn p bnd]|cs]; simpl in H |- *; try exact H.
    - rewrite vars_in_rewrap. apply (IH (esize n)); simpl; auto; lia.
    - apply (IH (esize n)); simpl; auto; lia.
    - apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      rewrite forallb_forall in H. apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc'].
Qed.

Lemma vars_in_of_components: forall P cs, (forall c, In c cs -> vars_in P c = true) -> vars_in P (of_components env cs) = true.
Proof.
    intros P cs H. assert (Hi: forallb (vars_in P) (map (fun c => with_mutability env
            (fold_left intersect_mutability (map (assignment_mutability env) cs) readonly) (without_null env c)) cs) = true).
    { apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      apply vars_in_set_mutability. rewrite vars_in_without_null. exact (H c' Hc'). }
    assert (Hk: forallb (vars_in P) (map (with_mutability env
            (fold_left intersect_mutability (map (assignment_mutability env) cs) readonly)) cs) = true).
    { apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      apply vars_in_set_mutability. exact (H c' Hc'). }
    destruct cs as [|c [|c' cs']]; [reflexivity|exact (H c (or_introl eq_refl))|].
    unfold of_components. destruct (negb (forallb (is_nullable env) _)); [exact Hi|].
    destruct (forallb is_nullable_type _); [exact Hi|exact Hk].
Qed.

Lemma vars_in_intersected: forall P t, vars_in P t = true -> forall c, In c (intersected_components t) -> vars_in P c = true.
Proof.
    intros P t H c Hc. destruct t as [| [] | | | | |cs]; simpl in Hc;
        try (destruct Hc as [<-|[]]; exact H).
    - apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']]. simpl in H |- *. rewrite forallb_forall in H. exact (H c' Hc').
    - simpl in H. rewrite forallb_forall in H. exact (H c Hc).
Qed.

Lemma vars_in_final_argument: forall P a, vars_in P a = true -> vars_in P (final_argument a) = true.
Proof. intros P [| | | |v o x| |] H; try exact H. unfold final_argument. destruct (_ || _); exact H. Qed.

(* Instantiated, a type has the type variables of the bindings, and those it has without a binding *)
Lemma vars_in_instantiate_h: forall (P P': TypeParameterId -> bool) U b t,
    (forall g, variables_of g = [] -> vars_in P' (U g) = true) ->
    (forall p a, lookup_binding b p = Some a -> vars_in P' a = true) ->
    (forall q, P q = true -> lookup_binding b q = None -> P' q = true) ->
    vars_in P t = true -> vars_in P' (instantiate_h env U b t) = true.
Proof.
    intros P P' U b t HU Hb HP. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; simpl in H.
    - simpl. apply forallb_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as [a' [<- Ha']].
      rewrite forallb_forall in H.
      apply (IH (esize a')); [pose proof (esize_in args a' Ha'); simpl; lia|reflexivity|apply H, Ha'].
    - simpl. rewrite vars_in_rewrap. apply (IH (esize n)); simpl; auto.
    - destruct vs; [|discriminate H]. simpl.
      assert (Hf: vars_in P' (match lookup_binding b p with Some a => final_argument a | None => U (mkGenericRef gm nn p []) end) = true).
      { destruct (lookup_binding b p) eqn:E; [exact (vars_in_final_argument P' e (Hb p e E))|apply HU; reflexivity]. }
      destruct nn; [rewrite vars_in_without_null|]; (destruct gm; [apply vars_in_set_mutability|]; exact Hf).
    - reflexivity.
    - simpl. assert (Hn: vars_in P' (instantiate_h env U b n) = true) by (apply (IH (esize n)); simpl; auto).
      destruct (instantiate_h env U b n) as [mi ci ai|ni|gi|mei msgi|vi oi ni|gi|csi] eqn:E;
          cbn beta iota zeta;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
          simpl in Hn |- *; rewrite ?vars_in_rewrap; simpl in Hn |- *;
          try reflexivity; try exact Hn; try (rewrite ?andb_true_r; exact Hn).
    - simpl. destruct vs; [|rewrite andb_false_r in H; discriminate H]. rewrite andb_true_r in H.
      destruct (lookup_binding b p) eqn:E; [|simpl; rewrite (HP p H E); reflexivity].
      pose proof (vars_in_final_argument P' e (Hb p e E)) as Hf.
      destruct nn; [rewrite vars_in_without_null|]; (destruct gm; [apply vars_in_set_mutability|]; exact Hf).
    - simpl. apply (intersect_instances_keeps env (vars_in P')); [apply vars_in_of_components|apply vars_in_intersected|reflexivity|].
      intros i Hi. apply in_map_iff in Hi. destruct Hi as [c' [<- Hc']]. rewrite forallb_forall in H.
      apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc'].
Qed.

Lemma vars_in_instantiate: forall (P P': TypeParameterId -> bool) b t,
    (forall p a, lookup_binding b p = Some a -> vars_in P' a = true) ->
    (forall q, P q = true -> lookup_binding b q = None -> P' q = true) ->
    vars_in P t = true -> vars_in P' (instantiate env b t) = true.
Proof.
    intros P P' b t Hb HP H. rewrite instantiate_top. apply (vars_in_instantiate_h P); [|exact Hb|exact HP|exact H].
    intros g Hg. unfold instantiate_unbound, through. generalize (S (rank_of env g)) as k. intros k. revert g Hg.
    induction k as [|k IHk]; intros g Hg; [reflexivity|]. cbn [through_level].
    apply (vars_in_instantiate_h (fun _ => false)); [exact IHk|exact Hb|intros q E; discriminate E|].
    apply no_vars_in. apply (no_vars_effective_bound env wf). destruct g as [gm nn p vs]. cbn [variables_of] in Hg. subst vs. reflexivity.
Qed.

(* The static upper bound of a variable with a candidate for the variable, of type variables of the
   bound but the variable itself *)
Lemma candidate_vars: forall (P: TypeParameterId -> bool) p c S, vars_in P S = true -> no_vars c = true ->
    vars_in (fun q => P q && negb (param_eqb q p)) (with_candidate env p c S) = true.
Proof.
    intros P p c S HS Hc. unfold with_candidate. apply (vars_in_instantiate P); [|intros q Hq E|exact HS].
    - intros q a Ha. simpl in Ha. destruct (param_eqb q p); [|discriminate Ha]. injection Ha as <-. simpl. exact (no_vars_in _ c Hc).
    - rewrite Hq. simpl in E |- *. destruct (param_eqb q p); [discriminate E|reflexivity].
Qed.

Lemma normalized_vars_in: forall P ca aargs ct, forallb (vars_in P) aargs = true ->
    forall a, In a (parameterized_supertype_arguments env ca aargs ct) -> vars_in P a = true.
Proof.
    intros P ca aargs ct Haargs a Ha. unfold parameterized_supertype_arguments in Ha.
    pose proof (supertypes_mention_no_variables ca ct) as Hs. unfold supertype_arguments in Hs.
    destruct (parameterized_supertype env ca ct) as [m c sargs| | | | | |]; try destruct Ha.
    apply in_map_iff in Ha. destruct Ha as [r [<- Hr]]. apply (vars_in_instantiate (fun _ => false)); [| |exact (no_vars_in _ _ (Hs r Hr))].
    - intros p a' Ha'. rewrite forallb_forall in Haargs. apply Haargs. exact (lookup_combine_in _ _ p a' Ha').
    - intros q E. discriminate E.
Qed.

End VarsIn.

Section Ranks.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.

Definition rank_below (r: nat) (q: TypeParameterId): bool := Nat.ltb (parameter_rank env q) r.

(* What a static upper bound of the variable p mentions: type variables of a lower rank, and the
   variable itself (`T : Comparable<T>`) *)
Definition static_vars (p: TypeParameterId) (q: TypeParameterId): bool := param_eqb q p || rank_below (parameter_rank env p) q.

(* The bounds of the variables without type variables, the static upper bounds as above *)
Definition ranked_states (s: VariableStates): Prop :=
    forall q st, lookup_state s q = Some st ->
        no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
        /\ vars_in (static_vars q) (static_upper_bound st) = true.

(* The states of the variables of rank r or above stay as they are *)
Definition keeps_from (r: nat) (s s': VariableStates): Prop :=
    forall q, r <= parameter_rank env q -> lookup_state s' q = lookup_state s q.

(* One of the types has no type variables, the other those of a rank below r *)
Definition one_side (r: nat) (t a: EType): Prop :=
    (no_vars t = true /\ vars_in (rank_below r) a = true) \/ (vars_in (rank_below r) t = true /\ no_vars a = true).

Lemma keeps_from_refl: forall r s, keeps_from r s s.
Proof. intros r s q _. reflexivity. Qed.

Lemma keeps_from_trans: forall r s1 s2 s3, keeps_from r s1 s2 -> keeps_from r s2 s3 -> keeps_from r s1 s3.
Proof. intros r s1 s2 s3 H1 H2 q Hq. rewrite (H2 q Hq). exact (H1 q Hq). Qed.

Lemma keeps_from_mono: forall r r' s s', r <= r' -> keeps_from r s s' -> keeps_from r' s s'.
Proof. intros r r' s s' Hr H q Hq. apply H. lia. Qed.

Lemma keeps_from_set: forall r s p st, rank_below r p = true -> keeps_from r s (set_state s p st).
Proof.
    intros r s p st Hp q Hq. unfold rank_below in Hp. apply Nat.ltb_lt in Hp.
    apply lookup_set_other. intros ->. lia.
Qed.

Lemma ranked_set: forall s p st, ranked_states s ->
    no_vars (upper_bound st) = true -> no_vars (lower_bound st) = true -> vars_in (static_vars p) (static_upper_bound st) = true ->
    ranked_states (set_state s p st).
Proof.
    intros s p st Hs Hu Hlo Hst q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. auto.
    - rewrite lookup_set_other in Hq by exact Hne. exact (Hs q st' Hq).
Qed.

Lemma one_side_swap: forall r t a, one_side r t a -> one_side r a t.
Proof. intros r t a [[H1 H2]|[H1 H2]]; [right|left]; split; assumption. Qed.

Lemma one_side_closed: forall r t a, no_vars t = true -> no_vars a = true -> one_side r t a.
Proof. intros r t a Ht Ha. left. split; [exact Ht|exact (no_vars_in _ a Ha)]. Qed.

(* The variable of a static upper bound, replaced by a candidate without type variables *)
Lemma candidate_below: forall p c S, vars_in (static_vars p) S = true -> no_vars c = true ->
    vars_in (rank_below (parameter_rank env p)) (with_candidate env p c S) = true.
Proof.
    intros p c S HS Hc. apply (vars_in_mono (fun q => static_vars p q && negb (param_eqb q p))); [|exact (candidate_vars env wf _ p c _ HS Hc)].
    intros q E. apply andb_true_iff in E. destruct E as [E1 E2]. unfold static_vars in E1.
    destruct (param_eqb q p); [discriminate E2|exact E1].
Qed.

Section KeepsFrom.

Variable f: UnifyFn.
Hypothesis Hf: forall r t a s s', ranked_states s -> one_side r t a -> f t a (Ongoing s) = Some (Ongoing s') ->
    keeps_from r s s' /\ ranked_states s'.
Hypothesis Hff: forall t a, f t a Failed = Some Failed.

Lemma fold_keeps_from: forall {A: Type} (h: Unification -> A -> option Unification) (l: list A) r s s',
    (forall x s0 s0', In x l -> ranked_states s0 -> h (Ongoing s0) x = Some (Ongoing s0') -> keeps_from r s0 s0' /\ ranked_states s0') ->
    (forall x, In x l -> h Failed x = Some Failed) ->
    ranked_states s -> fold_unify h l (Ongoing s) = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros A h l. induction l as [|x l IH]; intros r s s' Hh Hfail Hs H; simpl in H.
    - injection H as <-. split; [apply keeps_from_refl|exact Hs].
    - destruct (h (Ongoing s) x) as [[w|]|] eqn:E; try discriminate H.
      + destruct (Hh x s w (or_introl eq_refl) Hs E) as [K1 Hw].
        destruct (IH r w s' (fun y s0 s0' Hy => Hh y s0 s0' (or_intror Hy)) (fun y Hy => Hfail y (or_intror Hy)) Hw H) as [K2 Hs'].
        split; [exact (keeps_from_trans _ _ _ _ K1 K2)|exact Hs'].
      + rewrite (fold_failed h l (fun y Hy => Hfail y (or_intror Hy))) in H. discriminate H.
Qed.

Lemma find_first_keeps_from: forall (h: EType -> option Unification) (l: list EType) r s c s',
    (forall x s0, In x l -> h x = Some (Ongoing s0) -> keeps_from r s s0 /\ ranked_states s0) ->
    find_first h l = Some (Some (c, s')) -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros h l. induction l as [|x l IH]; intros r s c s' Hh H; simpl in H; [discriminate H|].
    destruct (h x) as [[w|]|] eqn:E; try discriminate H.
    - injection H as <- <-. exact (Hh x w (or_introl eq_refl) E).
    - exact (IH r s c s' (fun y s0 Hy => Hh y s0 (or_intror Hy)) H).
Qed.

Lemma flipped_keeps_from: forall r target cs s s', ranked_states s -> (forall c, In c cs -> one_side r target c) ->
    intersection_flipped_unify f target cs s = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r target cs s s' Hs Hcs H. unfold intersection_flipped_unify in H.
    destruct (find_first (fun c => f target c (Ongoing s)) cs) as [[[c w]|]|] eqn:E; try discriminate H.
    injection H as <-. apply (find_first_keeps_from (fun c => f target c (Ongoing s)) cs r s c w); [|exact E].
    intros x s0 Hx E0. exact (Hf r target x s s0 Hs (Hcs x Hx) E0).
Qed.

Lemma pairs_keeps_from: forall r targs aargs s s', ranked_states s ->
    ((forallb no_vars targs = true /\ forallb (vars_in (rank_below r)) aargs = true)
        \/ (forallb (vars_in (rank_below r)) targs = true /\ forallb no_vars aargs = true)) ->
    unify_arguments f targs aargs s = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r targs aargs s s' Hs Hside H. unfold unify_arguments in H.
    apply (fold_keeps_from (fun inner '(target, assignee) => f target assignee inner) (combine targs aargs) r s s'); [| |exact Hs|exact H].
    - intros [t a] s0 s0' Hin Hs0 E. apply in_combine_l in Hin as Hl. apply in_combine_r in Hin as Hr.
      apply (Hf r t a s0 s0' Hs0); [|exact E].
      destruct Hside as [[H1 H2]|[H1 H2]]; rewrite forallb_forall in H1, H2; [left|right]; split; auto.
    - intros [t a] _. apply Hff.
Qed.

Lemma static_check_keeps_from: forall r s st p c s', ranked_states s ->
    vars_in (static_vars p) (static_upper_bound st) = true -> rank_below r p = true -> no_vars c = true ->
    plus_static_check env f st p c (Ongoing s) = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r s st p c s' Hs HS Hp Hc H. unfold plus_static_check in H. destruct (no_vars (static_upper_bound st)).
    - injection H as <-. split; [apply keeps_from_refl|exact Hs].
    - destruct (Hf (parameter_rank env p) _ _ s s' Hs (or_intror (conj (candidate_below p c _ HS Hc) Hc)) H) as [K Hs'].
      split; [|exact Hs']. apply (keeps_from_mono (parameter_rank env p)); [|exact K].
      unfold rank_below in Hp. apply Nat.ltb_lt in Hp. lia.
Qed.

Lemma binding_check_keeps_from: forall r s st p B s', ranked_states s ->
    vars_in (static_vars p) (static_upper_bound st) = true -> rank_below r p = true -> no_vars B = true ->
    plus_binding_check env f st p B (Ongoing s) = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r s st p B s' Hs HS Hp HB H. unfold plus_binding_check in H.
    destruct B as [| | | |[] o t| |]; try (injection H as <-; split; [apply keeps_from_refl|exact Hs]).
    exact (static_check_keeps_from r s st p t s' Hs HS Hp HB H).
Qed.

Lemma plus_supertype_keeps_from: forall r s p A s', ranked_states s -> rank_below r p = true -> no_vars A = true ->
    plus_supertype_constraint env f s p A = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r s p A s' Hs Hp HA H. unfold plus_supertype_constraint in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (Hs p st Hl) as [Hnu [Hnl HS]].
    destruct (is_exact st) eqn:He; [exact (Hf r _ _ s s' Hs (one_side_closed r _ _ Hnl HA) H)|]. cbn zeta in H.
    pose proof (supertype_no_vars _ _ Hnl HA) as Hnc.
    destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E; cbn beta iota in H; try discriminate H.
    destruct (Hf r _ _ s w Hs (one_side_closed r _ _ Hnu Hnc) E) as [K1 Hw].
    destruct (plus_static_check env f st p _ (Ongoing w)) as [[w2|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (static_check_keeps_from r w st p _ w2 Hw HS Hp Hnc E2) as [K2 Hw2]. injection H as <-.
    split; [exact (keeps_from_trans _ _ _ _ (keeps_from_trans _ _ _ _ K1 K2) (keeps_from_set r w2 p _ Hp))|].
    apply (ranked_set w2 p); [exact Hw2|exact Hnu|exact Hnc|exact HS].
Qed.

Lemma plus_subtype_keeps_from: forall r s p U s', ranked_states s -> rank_below r p = true -> no_vars U = true ->
    plus_subtype_constraint env f s p U = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r s p U s' Hs Hp HU H. unfold plus_subtype_constraint in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (Hs p st Hl) as [Hnu [Hnl HS]].
    destruct (is_exact st) eqn:He; [exact (Hf r _ _ s s' Hs (one_side_closed r _ _ HU Hnu) H)|]. cbn zeta in H.
    pose proof (intersect_no_vars _ _ Hnu HU) as Hni.
    destruct (is_non_nullable_nothing env _); [discriminate H|].
    destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E; cbn beta iota in H; try discriminate H.
    destruct (Hf r _ _ s w Hs (one_side_closed r _ _ Hni Hnl) E) as [K1 Hw]. injection H as <-.
    split; [exact (keeps_from_trans _ _ _ _ K1 (keeps_from_set r w p _ Hp))|].
    apply (ranked_set w p); [exact Hw|exact Hni|exact Hnl|exact HS].
Qed.

Lemma plus_exact_keeps_from: forall r s p B s', ranked_states s -> rank_below r p = true -> no_vars B = true ->
    plus_exact_binding env f s p B = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r s p B s' Hs Hp HB H. unfold plus_exact_binding in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (Hs p st Hl) as [Hnu [Hnl HS]].
    cbn zeta in H. destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E1; cbn beta iota in H; try discriminate H.
    destruct (f B (lower_bound st) (Ongoing s)) as [[w'|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    destruct (Hf r _ _ s w' Hs (one_side_closed r _ _ HB Hnl) E2) as [K1 Hw'].
    destruct (plus_binding_check env f st p B (Ongoing w')) as [[w2|]|] eqn:E3; cbn beta iota in H; try discriminate H.
    destruct (binding_check_keeps_from r w' st p B w2 Hw' HS Hp HB E3) as [K2 Hw2]. injection H as <-.
    split; [exact (keeps_from_trans _ _ _ _ (keeps_from_trans _ _ _ _ K1 K2) (keeps_from_set r w2 p _ Hp))|].
    apply (ranked_set w2 p); [exact Hw2|exact HB|exact HB|exact HS].
Qed.

Lemma capturable_variable: forall t s q, capturable t s = Some q -> exists gm nn vs, t = TypeVariable (mkGenericRef gm nn q vs).
Proof.
    intros [| | | | |[gm nn q' vs]|] s q H; simpl in H; try discriminate H.
    destruct (lookup_state s q'); [|discriminate H]. destruct (_ && _); [|discriminate H]. injection H as <-. eauto.
Qed.

Ltac nvt := first
    [ assumption | reflexivity | (simpl; assumption)
    | (rewrite no_vars_without_null; first [assumption|reflexivity|(simpl; assumption)])
    | (apply (no_vars_effective_bound env wf); first [assumption|reflexivity|(simpl; assumption)])
    | (match goal with |- no_vars (read_type ?v _) = true => destruct v; cbn [read_type]; first [assumption|reflexivity] end) ].

Ltac vit := first
    [ assumption | (apply no_vars_in; nvt) | (simpl; assumption)
    | (rewrite vars_in_without_null; first [assumption|(simpl; assumption)])
    | (match goal with |- vars_in _ (read_type ?v _) = true =>
        destruct v; cbn [read_type]; first [assumption|(apply no_vars_in; reflexivity)] end) ].

Ltac os := first [ left; split; [nvt|vit] | right; split; [vit|nvt] ].

Ltac rk := match goal with
    | H: rank_below ?r ?q && _ = true |- rank_below ?r ?q = true => exact (proj1 (proj1 (andb_true_iff _ _) H))
    | H: vars_in (rank_below ?r) (TypeVariable (mkGenericRef _ _ ?q _)) = true |- rank_below ?r ?q = true =>
        simpl in H; exact (proj1 (proj1 (andb_true_iff _ _) H))
    end.

Ltac flip_side := let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc;
    match goal with
    | Ha: forallb _ ?cs = true, Hc: In ?c ?cs |- _ =>
        pose proof (proj1 (forallb_forall _ _) Ha c Hc); first [left; split; [nvt|assumption] | right; split; [vit|assumption]]
    end.

Ltac kf H :=
    repeat match type of H with
    | Some (Ongoing _) = Some (Ongoing _) => injection H as <-; split; [apply keeps_from_refl|assumption]
    | Some Failed = _ => discriminate H
    | None = _ => discriminate H
    | f ?x ?y (Ongoing ?s0) = Some (Ongoing ?s1) =>
        match goal with |- keeps_from ?r _ _ /\ _ => exact (Hf r x y s0 s1 ltac:(assumption) ltac:(os) H) end
    | plus_subtype_constraint env f ?s0 ?q ?u = _ =>
        match goal with |- keeps_from ?r _ _ /\ _ => exact (plus_subtype_keeps_from r s0 q u _ ltac:(assumption) ltac:(rk) ltac:(nvt) H) end
    | plus_supertype_constraint env f ?s0 ?q ?u = _ =>
        match goal with |- keeps_from ?r _ _ /\ _ => exact (plus_supertype_keeps_from r s0 q u _ ltac:(assumption) ltac:(rk) ltac:(nvt) H) end
    | type_variable_flipped_unify env f ?u ?q ?s0 = _ =>
        match goal with |- keeps_from ?r _ _ /\ _ => exact (plus_subtype_keeps_from r s0 q u _ ltac:(assumption) ltac:(rk) ltac:(nvt) H) end
    | intersection_flipped_unify f ?u ?cs ?s0 = _ =>
        match goal with |- keeps_from ?r _ _ /\ _ => refine (flipped_keeps_from r u cs s0 _ ltac:(assumption) _ H); flip_side end
    | context [if ?c then _ else _] => destruct c
    end.

Lemma unify_step_keeps_from: forall r t a s s', ranked_states s -> one_side r t a ->
    unify_step env f t a s = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    intros r t a s s' Hs Hside H.
    destruct t as [mt ct targs|tn|[gt nnt pt bt]|mte msgt|vt ot tt|[gt nnt pt bt]|tcs]; unfold unify_step in H.
    - (* a class type *)
      unfold unify_root_resolved in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; try (kf H; fail).
      all: try (eapply (flipped_keeps_from r _ acs s s' Hs); [|exact H]; rewrite forallb_forall in Ha; intros c Hc;
          first [left; split; [exact Ht|exact (Ha c Hc)]|right; split; [exact Ht|exact (Ha c Hc)]]; fail).
      all: repeat match type of H with context [if ?c then _ else _] => destruct c end; try discriminate H;
          try (injection H as <-; split; [apply keeps_from_refl|exact Hs]; fail).
      all: refine (pairs_keeps_from r targs _ s s' Hs _ H);
          first [ left; split; [exact Ht|first [exact Ha|apply forallb_forall; apply (normalized_vars_in env wf); exact Ha]]
                | right; split; [exact Ht|first [exact Ha|apply forallb_forall; intros a' Ha'; apply (normalized_no_vars env wf ca aargs ct Ha a' Ha')]] ].
    - (* a nullable type *)
      unfold unify_nullable in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; kf H.
    - (* a type parameter *)
      unfold unify_generic in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; try (kf H; fail).
    - (* an erroneous type *)
      unfold unify_erroneous in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; kf H.
    - (* a type argument *)
      unfold unify_type_argument in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; cbn [negb andb] in H; try (kf H; fail).
      all: try (eapply (flipped_keeps_from r _ acs s s' Hs); [|exact H]; rewrite forallb_forall in Ha; intros c Hc;
          first [left; split; [exact Ht|exact (Ha c Hc)]|right; split; [exact Ht|exact (Ha c Hc)]]; fail).
      all: destruct (negb (ownership_is_assignable_to oa ot)); [discriminate H|].
      all: destruct vt, va; cbn beta iota in H; try (kf H; fail).
      all: destruct (capturable tt s) as [q|] eqn:Ec.
      all: try (destruct (capturable_variable _ _ _ Ec) as [gm [nn [vs ->]]];
          first [ simpl in Ht; discriminate Ht
                | refine (plus_exact_keeps_from r s q _ s' Hs _ _ H); [rk|simpl; assumption] ]).
      all: cbn beta iota in H; try discriminate H.
      all: destruct (f tt ta (Ongoing s)) as [[w|]|] eqn:Ew; cbn beta iota in H; try discriminate H; [|rewrite Hff in H; discriminate H].
      all: destruct (Hf r tt ta s w Hs ltac:(os) Ew) as [K1 Hw];
          destruct (Hf r ta tt w s' Hw ltac:(os) H) as [K2 Hs']; split; [exact (keeps_from_trans _ _ _ _ K1 K2)|exact Hs'].
    - (* a type variable *)
      unfold unify_type_variable in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs];
          destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha;
          cbn beta iota zeta in H; kf H.
    - (* an intersection *)
      assert (Hx: forall x, In x tcs -> vars_in (rank_below r) x = true /\ one_side r x a).
      { intros x Hin. destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht; rewrite forallb_forall in Ht.
        - split; [exact (no_vars_in _ _ (Ht x Hin))|left; split; [exact (Ht x Hin)|exact Ha]].
        - split; [exact (Ht x Hin)|right; split; [exact (Ht x Hin)|exact Ha]]. }
      assert (Hone: forall x a', In x tcs -> (one_side r x a \/ no_vars a' = true) -> a' = a \/ no_vars a' = true -> one_side r x a').
      { intros x a' Hin _ [->|Ha']; [exact (proj2 (Hx x Hin))|right; split; [exact (proj1 (Hx x Hin))|exact Ha']]. }
      unfold unify_intersection, intersection_body in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; cbn beta iota zeta in H;
          try (destruct Hside as [[Ht Ha]|[Ht Ha]]; simpl in Ht, Ha; try discriminate Ht; try discriminate Ha; kf H; fail).
      (* a nullable assignee, where the intersection may be null *)
      all: try (match type of H with (if ?c then _ else _) = _ => destruct c; [discriminate H|] end).
      all: match type of H with context [fold_unify ?h ?l (Ongoing ?q0)] =>
          destruct (fold_unify h l (Ongoing q0)) as [[s2|]|] eqn:E1; cbn beta iota in H; try discriminate H end.
      all: assert (K1: keeps_from r s s2 /\ ranked_states s2) by
          (refine (fold_keeps_from _ _ r s s2 _ _ Hs E1);
           [ intros x y1 y2 Hin Hy1 E0; apply filter_In in Hin; refine (Hf r _ _ y1 y2 Hy1 _ E0); exact (proj2 (Hx x (proj1 Hin)))
           | intros x _; apply Hff ]).
      all: destruct K1 as [K1 Hs2].
      all: match type of H with context [find_first ?h ?l] =>
          destruct (find_first h l) as [[[c s3]|]|] eqn:E2; cbn beta iota in H; try discriminate H end.
      all: try (assert (K2: keeps_from r s2 s3 /\ ranked_states s3) by
          (refine (find_first_keeps_from _ _ r s2 c s3 _ E2);
           intros x y1 Hin E0; apply filter_In in Hin; refine (Hf r _ _ s2 y1 Hs2 _ E0); exact (proj2 (Hx x (proj1 Hin))));
          destruct K2 as [K2 Hs3]).
      (* a type variable among the components, unified with Any, or with the assignee where that fails *)
      all: repeat match type of H with context [if ?c then _ else _] => destruct c end.
      all: match type of H with fold_unify ?h ?l (Ongoing ?q3) = _ =>
          assert (K3: keeps_from r q3 s' /\ ranked_states s') by
              (refine (fold_keeps_from h l r q3 s' _ _ ltac:(first [exact Hs3|exact Hs2]) H);
               [ intros x y1 y2 Hin Hy1 E0; apply filter_In in Hin; destruct Hin as [Hin _]; cbn beta in E0;
                 match type of E0 with context [match f ?t ?na ?c0 with _ => _ end] =>
                     destruct (f t na c0) as [[?|]|] eqn:E3 in E0; cbn iota in E0;
                     [ injection E0 as <-; refine (Hf r _ _ y1 _ Hy1 _ E3)
                     | first [discriminate E0|refine (Hf r _ _ y1 _ Hy1 _ E0)]
                     | discriminate E0 ];
                     apply (Hone x _ Hin (or_introl (proj2 (Hx x Hin)))); first [left; reflexivity|right; reflexivity]
                 end
               | intros x _; cbn beta; rewrite Hff; cbn iota; first [reflexivity|apply Hff] ])
          end.
      all: destruct K3 as [K3 Hs'].
      all: split; [|exact Hs'].
      all: first [exact (keeps_from_trans _ _ _ _ K1 (keeps_from_trans _ _ _ _ K2 K3))|exact (keeps_from_trans _ _ _ _ K1 K3)].
Qed.

End KeepsFrom.

(* unify on a type without type variables and one with those of a rank below r leaves the states of
   the variables of rank r and above as they are *)
Lemma unify_keeps_from: forall n r t a s s', ranked_states s -> one_side r t a ->
    unify env n t a (Ongoing s) = Some (Ongoing s') -> keeps_from r s s' /\ ranked_states s'.
Proof.
    induction n as [|n IH]; intros r t a s s' Hs Hside H; [discriminate H|].
    rewrite unify_step_once in H.
    exact (unify_step_keeps_from (unify env n) IH (unify_keeps_failure env n) r t a s s' Hs Hside H).
Qed.

End Ranks.

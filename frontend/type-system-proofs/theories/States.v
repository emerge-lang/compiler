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

Fixpoint esize (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments => S (list_sum (map esize arguments))
    | Nullable n => S (esize n)
    | Generic (mkGenericRef _ _ _ bound) | TypeVariable (mkGenericRef _ _ _ bound) => S (esize bound)
    | Error _ _ => 1
    | TypeArgument _ _ n => S (esize n)
    | Intersection components => S (list_sum (map esize components))
    end.

Lemma esize_in: forall (l: list EType) a, In a l -> esize a <= list_sum (map esize l).
Proof.
    intros l a H. induction l as [|x l IH]; [destruct H|]. simpl. destruct H as [->|H]; [lia|]. specialize (IH H). lia.
Qed.

Definition relabel (s': VariableStates) (r: Unification): Unification :=
    match r with Ongoing _ => Ongoing s' | Failed => Failed end.

Lemma no_vars_without_null: forall t, no_vars (without_null t) = no_vars t.
Proof.
    fix IH 1. intros [m c a|n|[gm nn p b]|m msg|v o n|g|cs]; try reflexivity; simpl; [apply IH|apply IH|apply IH].
Qed.

Lemma no_vars_rewrap: forall t, no_vars (rewrap_nullable t) = no_vars t.
Proof. intros [| | | | | |]; reflexivity. Qed.

Section Variables.

Variable env: Environment.
Hypothesis wf: wellformed env.

Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.

Lemma no_vars_set_mutability: forall m t, no_vars t = true -> no_vars (with_mutability env m t) = true.
Proof.
    intros m t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm nn p bnd]|me msg|v o n|[gm nn p bnd]|cs]; simpl in H |- *; try discriminate H.
    - exact H.
    - rewrite no_vars_rewrap. apply (IH (esize n)); simpl; auto; lia.
    - apply (IH (esize bnd)); simpl; auto; lia.
    - reflexivity.
    - apply (IH (esize n)); simpl; auto; lia.
    - apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      rewrite forallb_forall in H. apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc'].
Qed.

Lemma no_vars_of_components: forall cs, (forall c, In c cs -> no_vars c = true) -> no_vars (of_components env cs) = true.
Proof.
    intros cs H. assert (Hi: forallb no_vars (map (fun c => with_mutability env
            (fold_left intersect_mutability (map (assignment_mutability env) cs) readonly) (without_null c)) cs) = true).
    { apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      apply no_vars_set_mutability. rewrite no_vars_without_null. exact (H c' Hc'). }
    destruct cs as [|c [|c' cs']]; [reflexivity|exact (H c (or_introl eq_refl))|].
    unfold of_components. destruct (forallb is_nullable _); exact Hi.
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

Lemma no_vars_instantiate: forall b t, (forall p a, lookup_binding b p = Some a -> no_vars a = true) ->
    no_vars t = true -> no_vars (instantiate env b t) = true.
Proof.
    intros b t Hb. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm nn p bnd]|me msg|v o n|[gm nn p bnd]|cs]; simpl in H; try discriminate H.
    - simpl. apply forallb_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as [a' [<- Ha']].
      rewrite forallb_forall in H. apply (IH (esize a')); [pose proof (esize_in args a' Ha'); simpl; lia|reflexivity|apply H, Ha'].
    - simpl. rewrite no_vars_rewrap. apply (IH (esize n)); simpl; auto; lia.
    - simpl. assert (Hf: no_vars (match lookup_binding b p with Some a => final_argument a | None => instantiate env b bnd end) = true).
      { destruct (lookup_binding b p) eqn:E; [exact (no_vars_final_argument e (Hb p e E))|]. apply (IH (esize bnd)); simpl; auto; lia. }
      destruct nn; [rewrite no_vars_without_null|]; (destruct gm; [apply no_vars_set_mutability|]; exact Hf).
    - reflexivity.
    - simpl. assert (Hn: no_vars (instantiate env b n) = true) by (apply (IH (esize n)); simpl; auto; lia).
      destruct (instantiate env b n) as [mi ci ai|ni|gi|mei msgi|vi oi ni|gi|csi] eqn:E;
          cbn beta iota zeta;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
          simpl in Hn |- *; rewrite ?no_vars_rewrap; simpl in Hn |- *;
          try reflexivity; try exact Hn; try (rewrite ?andb_true_r; exact Hn).
    - simpl. apply no_vars_of_components. intros c Hc. apply in_flat_map in Hc. destruct Hc as [i [Hi Hc]].
      apply in_map_iff in Hi. destruct Hi as [c' [<- Hc']]. apply (no_vars_intersected _ ) in Hc; [exact Hc|].
      rewrite forallb_forall in H. apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc'].
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
    | rewrite no_vars_without_null; simpl; assumption ].

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
      unfold unify_intersection in H |- *.
      destruct (no_vars_filter tcs Ht) as [Hv Hnv].
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try (destruct (negb (is_nullable _)); [injection H as <-; reflexivity|]; free H);
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
   stay so, too *)
Definition keeps_exact (s s': VariableStates): Prop :=
    (forall p st, lookup_state s p = Some st -> is_exact st = true -> lookup_state s' p = Some st)
    /\ (forall p st, lookup_state s p = Some st -> is_exact st = false -> is_capturable st = false ->
        exists st', lookup_state s' p = Some st' /\ is_exact st' = false /\ is_capturable st' = false
            /\ static_upper_bound st' = static_upper_bound st).

Lemma keeps_exact_refl: forall s, keeps_exact s s.
Proof. intros s. split; [intros p st H _; exact H|]. intros p st H He Hc. exists st. auto. Qed.

Lemma keeps_exact_trans: forall s1 s2 s3, keeps_exact s1 s2 -> keeps_exact s2 s3 -> keeps_exact s1 s3.
Proof.
    intros s1 s2 s3 [H1 H1'] [H2 H2']. split; [intros p st Hl He; exact (H2 p st (H1 p st Hl He) He)|].
    intros p st Hl He Hc. destruct (H1' p st Hl He Hc) as [st' [Hl' [He' [Hc' Hs']]]].
    destruct (H2' p st' Hl' He' Hc') as [st'' [Hl'' [He'' [Hc'' Hs'']]]]. exists st''. rewrite Hs'' in *. auto.
Qed.

Lemma keeps_exact_set: forall s s' p st st', lookup_state s p = Some st -> is_exact st = false ->
    (is_capturable st = false -> is_exact st' = false /\ is_capturable st' = false
        /\ static_upper_bound st' = static_upper_bound st) ->
    keeps_exact s s' -> keeps_exact s (set_state s' p st').
Proof.
    intros s s' p st st' Hl He Hst [H H']. split.
    - intros q stq Hq Heq. destruct (Nat.eq_dec p q) as [<-|Hne].
      + rewrite Hl in Hq. injection Hq as <-. rewrite He in Heq. discriminate Heq.
      + rewrite lookup_set_other by exact Hne. exact (H q stq Hq Heq).
    - intros q stq Hq Heq Hcq. destruct (Nat.eq_dec p q) as [<-|Hne].
      + rewrite Hl in Hq. injection Hq as <-. exists st'. rewrite lookup_set_same. destruct (Hst Hcq). auto.
      + rewrite lookup_set_other by exact Hne. exact (H' q stq Hq Heq Hcq).
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

Lemma plus_supertype_keeps_exact: forall s p t s',
    plus_supertype_constraint env f s p t = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros s p t s' H. unfold plus_supertype_constraint in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (is_exact st) eqn:He; [exact (Hf _ _ _ _ H)|]. cbn zeta in H.
    destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E; cbn beta iota in H; try discriminate H. injection H as <-.
    refine (keeps_exact_set s w p st _ Hl He _ (Hf _ _ _ _ E)). intros Hc. split; [reflexivity|split; [exact Hc|reflexivity]].
Qed.

Lemma plus_exact_keeps_exact: forall s p t s',
    (forall st, lookup_state s p = Some st -> is_exact st = false /\ is_capturable st = true) ->
    plus_exact_binding f s p t = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros s p t s' Hp H. unfold plus_exact_binding in H. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H].
    destruct (Hp st eq_refl) as [He Hcap].
    cbn zeta in H. destruct (f _ _ (Ongoing s)) as [[w|]|] eqn:E1; cbn beta iota in H; try discriminate H.
    destruct (f t (lower_bound st) (Ongoing s)) as [[w'|]|] eqn:E2; cbn beta iota in H; try discriminate H.
    injection H as <-.
    refine (keeps_exact_set s w' p st _ Hl He _ (Hf _ _ _ _ E2)). intros Hc. rewrite Hcap in Hc. discriminate Hc.
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
    - unfold unify_intersection in H.
      destruct a as [ma ca aargs|an|[ga nna pa ba]|mae msga|va oa ta|[ga nna pa ba]|acs]; cbn beta iota zeta in H;
          try (keeps H; fail).
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

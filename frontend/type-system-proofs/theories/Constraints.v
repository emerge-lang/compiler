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
(* Inference, with type variables bound by constraints                                              *)
(*                                                                                                *)
(* The type parameters of a function are inferred from the arguments of an invocation: unify       *)
(* records the constraints the arguments put on them, as a lower and an upper bound per type        *)
(* variable (plus_supertype_constraint, plus_subtype_constraint). Whatever unify accepts, it        *)
(* accepts with the type variables replaced by any types within their bounds (invocation_sound);   *)
(* and the types TypeUnification.getFinalValueFor picks are within them (final_values_satisfy).    *)
(* Together with capturing the type arguments of a receiver (Inference.v), that makes calling a    *)
(* member function with type parameters of its own sound (member_call_with_type_parameters_sound). *)
(*                                                                                                *)
(* Which types the variables are replaced with (xfrag), and which the bounds are (bfrag), is left   *)
(* open: the class types of Transitivity.v (classes_as_replacements, no_vars_as_bounds), or the     *)
(* type parameters and intersections of Fragment.v, as FinalValues.v has them.                     *)
(*                                                                                                *)
(* On the way: unify on types without type variables neither changes the variable states nor      *)
(* depends on them (unify_free), and a variable bound exactly stays so (unify_keeps_exact).        *)
(*                                                                                                *)
(* The bounds are combined with closestCommonSupertypeWith and intersect, which the model takes as  *)
(* given (Environment). They are assumed to be the bounds they are meant to be: what the closest   *)
(* common supertype of a bound and a type is assignable to, each of them is assignable to; and what *)
(* is assignable to the intersection of a bound and a type is assignable to each of them. Neither  *)
(* makes up type variables.                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* No type variables, also not in the bounds of type parameters *)
Fixpoint no_vars (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb no_vars arguments
    | Nullable n => no_vars n
    | Generic (mkGenericRef _ _ bound) => no_vars bound
    | Error _ _ => true
    | TypeArgument _ _ n => no_vars n
    | TypeVariable _ => false
    | Intersection components => forallb no_vars components
    end.

Fixpoint esize (t: EType): nat :=
    match t with
    | RootResolved _ _ arguments => S (list_sum (map esize arguments))
    | Nullable n => S (esize n)
    | Generic (mkGenericRef _ _ bound) | TypeVariable (mkGenericRef _ _ bound) => S (esize bound)
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
    fix IH 1. intros [m c a|n|[gm p b]|m msg|v o n|g|cs]; try reflexivity; simpl; [apply IH|apply IH].
Qed.

Lemma no_vars_rewrap: forall t, no_vars (rewrap_nullable t) = no_vars t.
Proof. intros [| | | | | |]; reflexivity. Qed.

Section Variables.

Variable env: Environment.

Hypothesis supertypes_mention_no_variables: forall sub super t,
    In t (supertype_arguments env sub super) -> no_vars t = true.

Lemma no_vars_set_mutability: forall m t, no_vars t = true -> no_vars (with_mutability env m t) = true.
Proof.
    intros m t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm p bnd]|me msg|v o n|[gm p bnd]|cs]; simpl in H |- *; try discriminate H.
    - exact H.
    - rewrite no_vars_rewrap. apply (IH (esize n)); simpl; auto; lia.
    - apply (IH (esize bnd)); simpl; auto; lia.
    - reflexivity.
    - apply (IH (esize n)); simpl; auto; lia.
    - apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
      rewrite forallb_forall in H. apply (IH (esize c')); [pose proof (esize_in cs c' Hc'); simpl; lia|reflexivity|apply H, Hc'].
Qed.

Lemma no_vars_instantiate: forall b t, (forall p a, lookup_binding b p = Some a -> no_vars a = true) ->
    no_vars t = true -> no_vars (instantiate env b t) = true.
Proof.
    intros b t Hb. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [mt c args|n|[gm p bnd]|me msg|v o n|[gm p bnd]|cs]; simpl in H; try discriminate H.
    - simpl. apply forallb_forall. intros a Ha. apply in_map_iff in Ha. destruct Ha as [a' [<- Ha']].
      rewrite forallb_forall in H. apply (IH (esize a')); [pose proof (esize_in args a' Ha'); simpl; lia|reflexivity|apply H, Ha'].
    - simpl. rewrite no_vars_rewrap. apply (IH (esize n)); simpl; auto; lia.
    - simpl. assert (Hf: no_vars (match lookup_binding b p with Some a => a | None => instantiate env b bnd end) = true).
      { destruct (lookup_binding b p) eqn:E; [exact (Hb p e E)|]. apply (IH (esize bnd)); simpl; auto; lia. }
      destruct gm; [apply no_vars_set_mutability|]; exact Hf.
    - reflexivity.
    - simpl. assert (Hn: no_vars (instantiate env b n) = true) by (apply (IH (esize n)); simpl; auto; lia).
      destruct (instantiate env b n) as [mi ci ai|ni|gi|mei msgi|vi oi ni|gi|csi] eqn:E;
          cbn beta iota zeta;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end;
          repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
          simpl in Hn |- *; rewrite ?no_vars_rewrap; simpl in Hn |- *;
          try reflexivity; try exact Hn; try (rewrite ?andb_true_r; exact Hn).
    - simpl. apply forallb_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as [c' [<- Hc']].
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
    destruct t as [mt ct targs|tn|[gt pt bt]|mte msgt|vt ot tt|[gt pt bt]|tcs]; simpl in Ht; try discriminate Ht;
        unfold unify_step in H |- *.
    - (* a class type *)
      unfold unify_root_resolved in H |- *.
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha.
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
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try free H.
    - (* a type parameter *)
      unfold unify_generic in H |- *.
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try free H.
      + destruct (is_non_nullable_nothing env _ && _); injection H as <-; reflexivity.
      + injection H as <-. reflexivity.
      + destruct (param_eqb pa _); [|free H].
        match type of H with context [if ?c then _ else _] => destruct c end; injection H as <-; reflexivity.
      + (eapply flipped_free; [|exact Ha|exact H]; nv).
    - (* an erroneous type *)
      unfold unify_erroneous in H |- *.
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha; free H.
    - (* a type argument *)
      unfold unify_type_argument in H |- *.
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha;
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
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; simpl in Ha; try discriminate Ha;
          try (destruct (negb (is_nullable _)); [injection H as <-; reflexivity|]; free H);
          try free H.
      + inter (RootResolved ma ca aargs) H Ht Hv Hnv tcs s s'.
      + inter (Generic (mkGenericRef ga pa ba)) H Ht Hv Hnv tcs s s'.
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
    intros [| | | | |[gm q bnd]|] s p H; simpl in H; try discriminate H.
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
    destruct t as [mt ct targs|tn|[gt pt bt]|mte msgt|vt ot tt|[gt pt bt]|tcs]; unfold unify_step in H.
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
      destruct a as [ma ca aargs|an|[ga pa ba]|mae msga|va oa ta|[ga pa ba]|acs]; cbn beta iota zeta in H;
          try (keeps H; fail).
      all: match type of H with context [fold_unify ?h ?l (Ongoing ?q0)] =>
          destruct (fold_unify h l (Ongoing q0)) as [[s2|]|] eqn:E1; cbn beta iota in H; try discriminate H;
          assert (K1: keeps_exact s s2) by
              (apply (fold_keeps_exact h l s s2); [intros x y1 y2 _ E0; exact (Hf _ _ _ _ E0)|intros x _; apply Hff|exact E1])
          end.
      all: match type of H with context [find_first ?h ?l] =>
          destruct (find_first h l) as [[[c s3]|]|] eqn:E2; cbn beta iota in H; try discriminate H
          end.
      all: match type of H with fold_unify ?h ?l (Ongoing ?q3) = _ =>
          assert (K3: keeps_exact q3 s') by
              (apply (fold_keeps_exact h l q3 s'); [intros x y1 y2 _ E0; exact (Hf _ _ _ _ E0)|intros x _; apply Hff|exact H])
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
(* Constraints                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Section Constraints.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis supertypes_mention_nothing_as_bottom: forall sub super t,
    In t (supertype_arguments env sub super) -> nothing_is_bottom t = true.
Hypothesis supertypes_mention_no_variables: forall sub super t,
    In t (supertype_arguments env sub super) -> no_vars t = true.

(* The types the type variables are replaced with: of the fragment of Fragment.v, those of the fragment
   of Transitivity.v among them, and each assignable to itself *)
Variable xfrag: EType -> Prop.
Hypothesis xfrag_gfrag: forall x, xfrag x -> gfrag env x = true.
Hypothesis in_fragment_xfrag: forall x, in_fragment env x = true -> xfrag x.
Hypothesis xfrag_reflexive: forall x, xfrag x -> exists n, unify env n x x (Ongoing []) = Some (Ongoing []).

(* The bounds of the type variables: the types of the fragment of Transitivity.v among them, and
   their intersections and closest common supertypes with those *)
Variable bfrag: EType -> Prop.
Hypothesis in_fragment_bfrag: forall x, in_fragment env x = true -> bfrag x.
Hypothesis intersect_bfrag: forall a b, bfrag a -> in_fragment env b = true -> bfrag (intersect env a b).
Hypothesis supertype_bfrag: forall a b, bfrag a -> in_fragment env b = true -> bfrag (closest_common_supertype_with env a b).

(* What is assignable to the intersection of a bound and a type is assignable to each of them *)
Hypothesis intersect_is_below: forall a b x n, bfrag a -> in_fragment env b = true -> xfrag x ->
    unify env n (intersect env a b) x (Ongoing []) = Some (Ongoing []) ->
    (exists n', unify env n' a x (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' b x (Ongoing []) = Some (Ongoing [])).
(* What the closest common supertype of a bound and a type is assignable to, each of them is assignable to *)
Hypothesis supertype_is_above: forall a b x n, bfrag a -> in_fragment env b = true -> xfrag x ->
    unify env n x (closest_common_supertype_with env a b) (Ongoing []) = Some (Ongoing []) ->
    (exists n', unify env n' x a (Ongoing []) = Some (Ongoing [])) /\ (exists n', unify env n' x b (Ongoing []) = Some (Ongoing [])).
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.

Lemma fragment_no_vars: forall k,
    (forall t, depth t <= k -> in_fragment env t = true -> no_vars t = true)
    /\ (forall a, argument_depth a <= k -> argument_in_fragment env a = true -> no_vars a = true).
Proof.
    induction k as [|k [IHt IHa]].
    { split.
      - intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; simpl in Hd; lia.
      - intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia. }
    split.
    - intros t Hd Ht. destruct (fragment_cases env t Ht) as [[m [c [args ->]]]|[m [c [args [-> Ht']]]]].
      + destruct (root_in_fragment env _ _ _ Ht) as [_ Hargs]. simpl. apply forallb_forall. intros a Ha.
        pose proof (argument_depth_below m c args a Ha). apply IHa; [lia|apply Hargs, Ha].
      + rewrite depth_nullable in Hd. simpl.
        destruct (root_in_fragment env _ _ _ Ht') as [_ Hargs]. apply forallb_forall. intros a Ha.
        pose proof (argument_depth_below m c args a Ha). apply IHa; [lia|apply Hargs, Ha].
    - intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd |- *. apply IHt; [lia|exact Ha].
Qed.

Lemma in_fragment_no_vars: forall t, in_fragment env t = true -> no_vars t = true.
Proof. intros t. apply (proj1 (fragment_no_vars (depth t))). lia. Qed.

Lemma argument_in_fragment_no_vars: forall a, argument_in_fragment env a = true -> no_vars a = true.
Proof. intros a. apply (proj2 (fragment_no_vars (argument_depth a))). lia. Qed.

(* unify on types without type variables, at other variable states *)
Lemma at_states: forall n t a s s', no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s) -> unify env n t a (Ongoing s') = Some (Ongoing s').
Proof. intros n t a s s' Ht Ha H. exact (unify_free env supertypes_mention_no_variables n t a s s' _ Ht Ha H). Qed.

Lemma keeps_free: forall n t a s u, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing u) -> u = s /\ unify env n t a (Ongoing []) = Some (Ongoing []).
Proof.
    intros n t a s u Ht Ha H. split.
    - pose proof (unify_free env supertypes_mention_no_variables n t a s s _ Ht Ha H) as E. rewrite H in E.
      injection E as ->. reflexivity.
    - exact (unify_free env supertypes_mention_no_variables n t a s [] _ Ht Ha H).
Qed.

(* A type the variable is replaced with, within what the state of the variable allows: the types the
   type argument it is bound to exactly stands for, or the types between its bounds *)
Definition fits (st: VariableState) (o: Ownership) (x: EType): Prop :=
    if is_exact st then
        exists vb ob X K, upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ in_fragment env X = true /\ in_fragment env x = true
            /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing []) = Some (Ongoing [])
    else (exists K, unify env K x (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ (exists K, unify env K (upper_bound st) x (Ongoing []) = Some (Ongoing [])).

Definition satisfies (b: Bindings) (s: VariableStates): Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        xfrag x /\ exists st, lookup_state s p = Some st /\ fits st o x.

(* The variable states unify works with: the bounds without type variables, the upper bound above the
   lower one where the variable isn't bound exactly, and no variable to capture *)
(* What is below the upper bound of a variable is below its declared one *)
Definition below_static (st: VariableState): Prop :=
    forall x f, xfrag x -> unify env f (upper_bound st) x (Ongoing []) = Some (Ongoing []) ->
        exists f', unify env f' (static_upper_bound st) x (Ongoing []) = Some (Ongoing []).

Definition wf_states (s: VariableStates): Prop :=
    forall p st, lookup_state s p = Some st ->
        no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
        /\ (is_exact st = false -> is_capturable st = false
            /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
            /\ below_static st /\ bfrag (upper_bound st) /\ bfrag (lower_bound st)).

Lemma wf_set_state: forall s p st, wf_states s ->
    no_vars (upper_bound st) = true -> no_vars (lower_bound st) = true ->
    (is_exact st = false -> is_capturable st = false
        /\ (exists K, unify env K (upper_bound st) (lower_bound st) (Ongoing []) = Some (Ongoing []))
        /\ below_static st /\ bfrag (upper_bound st) /\ bfrag (lower_bound st)) ->
    wf_states (set_state s p st).
Proof.
    intros s p st Hs Hu Hl He q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. auto.
    - rewrite lookup_set_other in Hq by exact Hne. exact (Hs q st' Hq).
Qed.

Lemma satisfies_set_state: forall s p st st', lookup_state s p = Some st ->
    (forall o x, xfrag x -> fits st' o x -> fits st o x) ->
    forall b, satisfies b (set_state s p st') -> satisfies b s.
Proof.
    intros s p st st' Hl Hf b Hb q o x Hq. destruct (Hb q o x Hq) as [Hx [st'' [Hq' Hfit]]]. split; [exact Hx|].
    destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq'. injection Hq' as <-. exists st. split; [exact Hl|exact (Hf o x Hx Hfit)].
    - rewrite lookup_set_other in Hq' by exact Hne. exists st''. auto.
Qed.

Lemma not_capturable: forall s t, wf_states s -> capturable t s = None.
Proof.
    intros s [| | | | |[gm p bnd]|] Hs; try reflexivity. simpl.
    destruct (lookup_state s p) as [st|] eqn:E; [|reflexivity].
    destruct (is_exact st) eqn:Ee; [rewrite andb_false_r; reflexivity|].
    destruct (Hs p st E) as [_ [_ He]]. rewrite (proj1 (He Ee)). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A type variable, assigned to and assigned                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* What the variable takes: above the lower bound, which is above it *)
Lemma target_leaf: forall n p bnd st A s s', wf_states s -> lookup_state s p = Some st -> afrag env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f x A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' Hs Hl HAf H. destruct (Hs p st Hl) as [Hnu [Hnl He]].
    destruct (afrag_parts env A HAf) as [HA HAn].
    pose proof (in_fragment_no_vars A HA) as HnA.
    assert (H': plus_supertype_constraint env (unify env n) s p A = Some (Ongoing s')).
    { rewrite unify_step_once in H. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          unfold unify_step, unify_type_variable in H; [exact H|]. destruct (is_nullable _); [exact H|discriminate H]. }
    unfold plus_supertype_constraint in H'. rewrite Hl in H'. destruct (is_exact st) eqn:Ee.
    - (* bound exactly: its binding takes A *)
      destruct (keeps_free n _ A s s' Hnl HnA H') as [-> H0]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold fits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [HxF Hc]]]]]]]]. rewrite Hlo in H0.
      destruct (write_leaf env wf K [] n vb ob X o x A [] HX HxF HAf Hc H0) as [_ Hw]. exists (n + K + 1). exact Hw.
    - (* between bounds: the lower bound becomes the closest common supertype with A *)
      cbn zeta in H'.
      pose proof (supertype_no_vars _ _ Hnl HnA) as Hnn.
      destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free n _ _ s ns Hnu Hnn E) as [-> H0].
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      split; [|split].
      + apply wf_set_state; [exact Hs|exact Hnu|exact Hnn|]. intros _. split; [exact Hcap|]. split; [exists n; exact H0|].
        split; [exact Hbs|]. split; [exact Hbu|exact (supertype_bfrag _ _ Hbl HA)].
      + apply (satisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [[K1 E1] [K2 E2]]. split; [|exists K2; exact E2].
        exact (proj1 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold fits in Hfit. cbn [is_exact lower_bound] in Hfit.
        destruct Hfit as [[K1 E1] _]. exact (proj2 (supertype_is_above _ _ x K1 Hbl HA Hx E1)).
Qed.

(* What the variable is assigned to: below the upper bound, which is below it *)
Lemma assignee_leaf: forall n p bnd st A s s', wf_states s -> lookup_state s p = Some st -> in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None p bnd)) (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall o x, xfrag x -> (forall st', lookup_state s' p = Some st' -> fits st' o x) ->
        exists f, unify env f A x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n p bnd st A s s' Hs Hl HA H. destruct (Hs p st Hl) as [Hnu [Hnl He]].
    pose proof (in_fragment_no_vars A HA) as HnA.
    assert (H': plus_subtype_constraint env (unify env n) s p A = Some (Ongoing s')).
    { rewrite unify_step_once in H. destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
          exact H. }
    unfold plus_subtype_constraint in H'. rewrite Hl in H'. destruct (is_exact st) eqn:Ee.
    - (* bound exactly: A takes what its binding gives *)
      destruct (keeps_free n A _ s s' HnA Hnu H') as [-> H0]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold fits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [HxF Hc]]]]]]]]. rewrite Hu in H0.
      destruct (read_leaf env wf K [] n vb ob X o x A [] HX HxF HA Hc H0) as [_ Hr]. exists (n + K + 1). exact Hr.
    - (* between bounds: the upper bound becomes the intersection with A *)
      cbn zeta in H'.
      pose proof (intersect_no_vars _ _ Hnu HnA) as Hnn.
      destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
      destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free n _ _ s ns Hnn Hnl E) as [-> H0].
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      split; [|split].
      + apply wf_set_state; [exact Hs|exact Hnn|exact Hnl|]. intros _. split; [exact Hcap|]. split; [exists n; exact H0|].
        split; [|split; [exact (intersect_bfrag _ _ Hbu HA)|exact Hbl]].
        intros x f Hx Ex. destruct (intersect_is_below _ _ x f Hbu HA Hx Ex) as [[f1 E1] _]. exact (Hbs x f1 Hx E1).
      + apply (satisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold fits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [[K1 E1] [K2 E2]]. split; [exists K1; exact E1|].
        exact (proj1 (intersect_is_below _ _ x K2 Hbu HA Hx E2)).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold fits in Hfit. cbn [is_exact upper_bound] in Hfit.
        destruct Hfit as [_ [K2 E2]]. exact (proj2 (intersect_is_below _ _ x K2 Hbu HA Hx E2)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Pairs of type arguments                                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma combine_map_in: forall (f g: EType -> EType) (l1 l2: list EType) x y,
    In (x, y) (combine (map f l1) (map g l2)) -> exists t a, In (t, a) (combine l1 l2) /\ x = f t /\ y = g a.
Proof.
    intros f g l1. induction l1 as [|t l1 IH]; intros [|a l2] x y H; simpl in H; try destruct H.
    - injection H as <- <-. exists t, a. split; [left; reflexivity|split; reflexivity].
    - destruct (IH l2 x y H) as [t' [a' [Hin [-> ->]]]]. exists t', a'. split; [right; exact Hin|split; reflexivity].
Qed.

Lemma uniform_fuel: forall (l: list (EType * EType)) (Q: nat -> EType * EType -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

Lemma fold_from_pairs: forall f (l: list (EType * EType)),
    (forall t a, In (t, a) l -> unify env f t a (Ongoing []) = Some (Ongoing [])) ->
    fold_unify (fun inner '(t, a) => unify env f t a inner) l (Ongoing []) = Some (Ongoing []).
Proof.
    intros f l H. induction l as [|[t a] l IH]; [reflexivity|]. simpl. rewrite (H t a (or_introl eq_refl)).
    apply IH. intros t' a' Hin. apply H. right. exact Hin.
Qed.

Lemma fold_chain: forall n (l: list (EType * EType)) s s',
    (forall t a, In (t, a) l -> forall s0 s0', wf_states s0 -> unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
        wf_states s0' /\ (forall b, satisfies b s0' -> satisfies b s0)) ->
    wf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) l (Ongoing s) = Some (Ongoing s') ->
    wf_states s' /\ (forall b, satisfies b s' -> satisfies b s)
    /\ (forall t a, In (t, a) l -> exists s0 s0', wf_states s0 /\ unify env n t a (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b, satisfies b s' -> satisfies b s0')).
Proof.
    intros n l. induction l as [|[t a] l IH]; intros s s' Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros t a [].
    - destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hstep t a (or_introl eq_refl) s s1 Hs E) as [Hs1 Hext1].
      destruct (IH s1 s' (fun t' a' Hin => Hstep t' a' (or_intror Hin)) Hs1 H) as [Hs' [Hext Hpairs]].
      split; [exact Hs'|]. split; [intros b Hb; apply Hext1, Hext, Hb|].
      intros t' a' [E'|Hin].
      + injection E' as <- <-. exists s, s1. split; [exact Hs|]. split; [exact E|exact Hext].
      + exact (Hpairs t' a' Hin).
Qed.

Lemma state_of_target: forall n p bnd A s r, in_fragment env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None p bnd)) A (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_type_variable, plus_supertype_constraint in H; [rewrite E in H; discriminate H|].
    destruct (is_nullable _); [rewrite E in H|]; discriminate H.
Qed.

Lemma state_of_assignee: forall n p bnd A s r, in_fragment env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None p bnd)) (Ongoing s) = Some (Ongoing r) -> exists st, lookup_state s p = Some st.
Proof.
    intros n p bnd A s r HA H. destruct (lookup_state s p) as [st|] eqn:E; [eauto|exfalso].
    rewrite unify_step_once in H.
    destruct (fragment_cases env A HA) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        unfold unify_step, unify_root_resolved, unify_nullable, type_variable_flipped_unify, plus_subtype_constraint in H;
        rewrite E in H; discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Soundness                                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

Section Main.

(* The types the type variables are replaced with, and the fuel with which they are within the
   bounds of the type parameters *)
Variable b: Bindings.
Variable K: nat.

Lemma constraints_with_arguments: forall n,
    (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', ifrag env P = true -> afrag env A = true -> closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f A (inst env b P) (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_in_fragment env A = true -> nothing_is_bottom A = true ->
        closed A = true -> bound_in env b K [] (to_generic P) = true ->
        wf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    (* the parts of the types of the arguments *)
    assert (Hargs: forall ma ca aargs, in_fragment env (RootResolved ma ca aargs) = true ->
        nothing_is_bottom (RootResolved ma ca aargs) = true -> closed (RootResolved ma ca aargs) = true ->
        length aargs = length (parameter_ids env ca) /\ forall a, In a aargs ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ma ca aargs Hf Hn Hc. destruct (root_in_fragment env ma ca aargs Hf) as [Hl Ha]. split; [exact Hl|].
      intros a Hin. split; [exact (Ha a Hin)|]. split; [exact (proj2 (nothing_is_bottom_root ma ca aargs Hn) a Hin)|].
      exact (closed_parts ma ca aargs Hc a Hin). }
    assert (Hnorm: forall ca ct aargs, ca <> ct -> ca <> nothing -> base_type_is_subtype_of env ca ct = true ->
        length aargs = length (parameter_ids env ca) ->
        (forall a, In a aargs -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true) ->
        forall a, In a (parameterized_supertype_arguments env ca aargs ct) ->
            argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
    { intros ca ct aargs Hne Hcn Hbase Hl Ha a Hin.
      assert (Hta: forall y, In y aargs -> is_type_argument y = true)
          by (intros y Hy; apply (argument_in_fragment_is_type_argument env), Ha, Hy).
      destruct (supertype_arguments_to_generic env wf supertypes_mention_nothing_as_bottom ca ct aargs Hne Hcn Hbase Hl Hta)
          as [_ [_ [Hnb Hcl]]].
      destruct (supertype_arguments_in_fragment env wf ca ct aargs Hne Hcn Hbase Hl (fun y Hy => proj1 (Ha y Hy))) as [_ Hf].
      split; [exact (Hf a Hin)|]. split; [apply Hnb; [intros y Hy; apply Ha, Hy|exact Hin]|apply Hcl; [intros y Hy; apply Ha, Hy|exact Hin]]. }
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        wf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, fold_unify (fun inner '(t, a) => unify env f t a inner)
            (combine (map inst_t targs) (map inst_a aargs)) (Ongoing []) = Some (Ongoing []))).
    { intros targs aargs s s' inst_t inst_a Hp Hs H.
      destruct (fold_chain n _ s s' (fun t a Hin s0 s0' Hs0 E => let H' := Hp t a Hin s0 s0' Hs0 E in conj (proj1 H') (proj1 (proj2 H')))
          Hs H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hb.
      destruct (uniform_fuel (combine targs aargs) (fun f '(t, a) => unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing [])))
          as [f Hf].
      - intros f f' [t a] Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E).
      - intros [t a] Hin. destruct (Hall t a Hin) as [s0 [s0' [Hs0 [E Hx]]]].
        exact (proj2 (proj2 (Hp t a Hin s0 s0' Hs0 E)) (Hx b Hb)).
      - exists f. apply fold_from_pairs. intros x y Hin. destruct (combine_map_in inst_t inst_a _ _ x y Hin) as [t [a [Hin' [-> ->]]]].
        exact (Hf (t, a) Hin'). }
    split; [|split; [|split]].
    - (* a type with type variables as the target *)
      intros P A s s' HP HA HcA Hb Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (satisfies b s' -> exists f, unify env f (inst env b (RootResolved mt ct targs)) (RootResolved ma ca aargs) (Ongoing [])
              = Some (Ongoing []))).
      { intros mt ct targs ma ca aargs Hft Hfa Hna Hca Hbt Hu.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft)).
        pose proof (root_parts env b K [] mt ct targs Hft Hbt) as Htargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_in_fragment env a = true /\ nothing_is_bottom a = true /\ closed a = true).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne). exact (Hnorm ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f (instantiate env b t) ((fun a => a) a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Htargs t Ht) as [Hft' Hbt']. destruct (Hnorm' a Ha) as [Hfa' [Hna' Hca']].
          exact (IHat t a s0 s0' Hft' Hfa' Hna' Hca' Hbt' Hs0 E). }
        destruct (Hpairs targs norm s s' (instantiate env b) (fun a => a) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_cases env P HP) as [[mt [ct [targs [-> _]]]]|[->|[[mt [ct [targs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          [| unfold bottom_type in * | |].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> _]]]]];
            [exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H)|rewrite unify_class_nullable in H; discriminate H].
      + assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP')).
        destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]].
        * rewrite unify_nullable_class in H. destruct (IHt _ _ s s' HP' HA HcA Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in Hf.
          exists (S f). rewrite unify_nullable_class. exact Hf.
        * rewrite unify_nullable_nullable in H.
          assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
          destruct (IHt _ _ s s' HP' HA2 HcA Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in Hf.
          exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + (* a type variable *)
        destruct (state_of_target n p bnd A s s' HA' H) as [st Hl].
        destruct (target_leaf n p bnd st A s s' Hs Hl HA H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
    - (* a type with type variables as the assignee *)
      intros P A s s' HP HA HcA Hb Hs H. destruct (afrag_parts env A HA) as [HA' HAn].
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          in_fragment env (RootResolved ma ca aargs) = true -> nothing_is_bottom (RootResolved ma ca aargs) = true ->
          closed (RootResolved ma ca aargs) = true -> bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
          /\ (satisfies b s' -> exists f, unify env f (RootResolved ma ca aargs) (inst env b (RootResolved mp cp pargs)) (Ongoing [])
              = Some (Ongoing []))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hna Hca Hbp Hu.
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp)).
        pose proof (root_parts env b K [] mp cp pargs Hfp Hbp) as Hpargs.
        destruct (Hargs ma ca aargs Hfa Hna Hca) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hnorm': (forall a, In a norm -> argument_ifrag env a = true /\ bound_in env b K [] (to_generic a) = true)
            /\ (if class_eqb cp ca then map (instantiate env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate env b) pargs) ca) = map (instantiate env b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [? [Heq _]]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables env wf supertypes_mention_nothing_as_bottom b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', wf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            wf_states s0' /\ (forall b', satisfies b' s0' -> satisfies b' s0)
            /\ (satisfies b s0' -> exists f, unify env f ((fun a => a) t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. destruct (Haargs t Ht) as [Hft' [Hnt' Hct']].
          exact (IHaa a t s0 s0' Hfa' Hft' Hnt' Hct' Hba' Hs0 E). }
        destruct (Hpairs aargs norm s s' (fun a => a) (instantiate env b) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (fragment_cases env A HA') as [[ma [ca [aargs ->]]]|[ma [ca [aargs [-> HA'']]]]];
      destruct (ifrag_cases env P HP) as [[mp [cp [pargs [-> _]]]]|[->|[[mp [cp [pargs [-> HP']]]]|[p [bnd [-> [Hfb Hcb]]]]]]];
          try (unfold bottom_type in *).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + exact (Hroot _ _ _ _ _ _ HP HA' HAn HcA Hb H).
      + rewrite unify_class_nullable in H. discriminate H.
      + destruct (state_of_assignee n p bnd _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p bnd st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hb Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        rewrite unify_nullable_class in H. destruct (IHa _ _ s s' HP HA2 HcA Hb Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
      + assert (HA2: afrag env (RootResolved ma ca aargs) = true) by (unfold afrag; rewrite HA''; exact HAn).
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
        rewrite unify_nullable_nullable in H. destruct (IHa _ _ s s' HP' HA2 HcA Hb' Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP')) in Hf.
        rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP')).
        exists (S f). rewrite unify_nullable_nullable. exact Hf.
      + destruct (state_of_assignee n p bnd _ s s' HA' H) as [st Hl].
        destruct (assignee_leaf n p bnd st _ s s' Hs Hl HA' H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        simpl in Hb. destruct (binds_exactly_some env b K [] p bnd Hb) as [o [x [Ex _]]].
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> fits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        destruct (Hsound o x Hx Hfits) as [f Hf]. rewrite (inst_variable env b p bnd _ _ _ Ex). exists f. exact Hf.
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hb Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (not_capturable s nt Hs)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      assert (Hown: ownership_is_assignable_to oa (instantiate_ownership b ot) = true).
      { pose proof (instantiation_preserves_ownership_assignability b oa ot Ho) as Ho'.
        rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (ifrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na s s1 HP HAf Hcn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHa nt na s1 s' HP HAf Hcn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHt nt top_type s s' HP (top_in_afrag env wf) eq_refl Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt bottom_type s s' HP (bottom_in_afrag env wf) eq_refl Hbn Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA HAn HcA Hb Hs H; try discriminate HP; try discriminate HA.
      simpl in HP, HA, HAn. destruct (bound_in_argument env b K [] vp op (to_generic np) Hb) as [_ Hbn].
      destruct (closed_argument va oa na HcA) as [Hoa Hcn].
      assert (HAf: afrag env na = true) by (unfold afrag; rewrite HA, HAn; reflexivity).
      rewrite (unify_type_arguments env n va oa na vp op np s (fragment_not_variable env _ HA)) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      assert (Hown: ownership_is_assignable_to (instantiate_ownership b op) oa = true).
      { pose proof (instantiation_preserves_ownership_assignability b op oa Ho) as Ho'.
        rewrite (ownership_not_instantiated b oa Hoa) in Ho'. exact Ho'. }
      assert (Hgoal: forall f, compare_variances (unify env f) va vp na (inst env b np) [] = Some (Ongoing []) ->
          unify env (S f) (TypeArgument va oa na) (instantiate env b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env b K [] vp op np HP Hbn).
        rewrite (unify_type_arguments env f va oa na vp _ (inst env b np) [] (fragment_not_variable env _ HA)), Hown. exact E. }
      pose proof (in_fragment_no_vars na HA) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHa np na s s1 HP HAf Hcn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHt np na s1 s' HP HAf Hcn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HAf Hcn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros _; exists (S k); apply Hgoal; unfold compare_variances; exact H0
            end ].
Qed.

End Main.

(* ---------------------------------------------------------------------------------------------- *)
(* Invocations                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * Inference is sound: where unify accepts each argument of an invocation for its parameter, in turn,
 * each argument fits its parameter with the type variables replaced by any types that satisfy the
 * variable states it ends with.
 *)
Theorem invocation_sound: forall n Ps As s0 u b K,
    wf_states s0 ->
    (forall P, In P Ps -> ifrag env P = true /\ bound_in env b K [] (to_generic P) = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    wf_states u /\ (satisfies b u ->
        forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true).
Proof.
    intros n Ps As s0 u b K Hs0 HPs HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', wf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        wf_states s' /\ (forall b', satisfies b' s' -> satisfies b' s)
        /\ (satisfies b s' -> exists f, unify env f (inst env b P) A (Ongoing []) = Some (Ongoing []))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP HbP]. destruct (HAs A HA) as [HfA HcA].
      exact (proj1 (constraints_with_arguments b K n) P A s s' HfP HfA HcA HbP Hs E). }
    destruct (fold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros Hb P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    destruct (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hb)) as [f Hf].
    exists f. unfold is_assignable_to, empty_unification. rewrite Hf. reflexivity.
Qed.

(* TypeUnification.getFinalValueFor: the lower bound, unless it is still Nothing, then the upper one *)
Definition final_value (st: VariableState): EType :=
    if is_non_nullable_nothing env (lower_bound st) then upper_bound st else lower_bound st.

(* The final value of a variable that isn't bound exactly is within its bounds, if it is one of the
   types variables are replaced with *)
Lemma final_value_fits: forall s p st o, wf_states s -> lookup_state s p = Some st -> is_exact st = false ->
    xfrag (final_value st) -> fits st o (final_value st).
Proof.
    intros s p st o Hs Hl He Hf. destruct (Hs p st Hl) as [_ [_ Hb]]. destruct (Hb He) as [_ [[K HK] _]].
    unfold fits. rewrite He. destruct (xfrag_reflexive _ Hf) as [k Hr].
    unfold final_value in Hf, Hr |- *. destruct (is_non_nullable_nothing env (lower_bound st)).
    - split; [exists K; exact HK|exists k; exact Hr].
    - split; [exists k; exact Hr|exists K; exact HK].
Qed.

(*
 * The types the type variables are replaced with, in the end: the final value of each variable that
 * isn't bound exactly, and any type the type argument of one that is stands for. They satisfy the
 * variable states, so each argument fits its parameter with them (invocation_sound).
 *)
Theorem final_values_satisfy: forall u b, wf_states u ->
    (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        xfrag x /\ exists st, lookup_state u p = Some st /\
            (is_exact st = false -> x = final_value st)
            /\ (is_exact st = true -> fits st o x)) ->
    satisfies b u.
Proof.
    intros u b Hu Hb p o x E. destruct (Hb p o x E) as [Hx [st [Hl [Hfin Hex]]]]. split; [exact Hx|].
    exists st. split; [exact Hl|]. destruct (is_exact st) eqn:Ee; [exact (Hex eq_refl)|].
    rewrite (Hfin eq_refl) in Hx |- *. exact (final_value_fits u p st o Hu Hl Ee Hx).
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* Member calls, with type parameters of the function                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Definition final_value_of (u: VariableStates) (p: TypeParameterId): EType :=
    match lookup_state u p with Some st => final_value st | None => bottom_type end.

Lemma lookup_for_inference: forall (vars: list (TypeParameterId * EType)) caps p bound, NoDup (map fst vars) -> In (p, bound) vars ->
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) caps))) vars) p
    = Some (mkVariableState bound bound bottom_type false (existsb (param_eqb p) caps)).
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_for_inference_in: forall (vars: list (TypeParameterId * EType)) caps p st,
    lookup_state (map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) caps))) vars) p = Some st ->
    exists bound, In (p, bound) vars.
Proof.
    intros vars caps. induction vars as [|[q bq] rest IH]; intros p st H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. exists bq. left. reflexivity.
    - destruct (IH p st H) as [bound Hin]. exists bound. right. exact Hin.
Qed.

Lemma nodup_app_l: forall (l1 l2: list TypeParameterId), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
    intros l1 l2. induction l1 as [|x l1 IH]; intros H; [constructor|]. inversion H as [|? ? Hnotin H2]. subst.
    constructor; [intros Hx; apply Hnotin, in_or_app; left; exact Hx|exact (IH H2)].
Qed.

Lemma nodup_app_disjoint: forall (l1 l2: list TypeParameterId) a, NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
    intros l1 l2 a. induction l1 as [|x l1 IH]; intros Hnd H1 H2; [destruct H1|]. inversion Hnd as [|? ? Hnotin Hnd2]. subst.
    destruct H1 as [->|H1]; [apply Hnotin, in_or_app; right; exact H2|exact (IH Hnd2 H1 H2)].
Qed.

Lemma lookup_app: forall (l1 l2: Bindings) p,
    lookup_binding (l1 ++ l2) p = match lookup_binding l1 p with Some a => Some a | None => lookup_binding l2 p end.
Proof.
    intros l1 l2 p. induction l1 as [|[q a] l1 IH]; [reflexivity|]. simpl. destruct (param_eqb p q); [reflexivity|exact IH].
Qed.

Lemma lookup_own: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId -> EType) p a,
    lookup_binding (map (fun v => (fst v, g (fst v))) l) p = Some a -> a = g p /\ In p (map fst l).
Proof.
    intros l g p a. induction l as [|[q bq] l IH]; intros H; simpl in H; [discriminate H|].
    destruct (param_eqb p q) eqn:E.
    - apply param_eqb_eq in E. subst q. injection H as <-. split; [reflexivity|left; reflexivity].
    - destruct (IH H) as [-> Hin]. split; [reflexivity|right; exact Hin].
Qed.

Lemma fold_keeps_exact_unify: forall nf (l: list (EType * EType)) s s',
    fold_unify (fun inner '(P, A) => unify env nf P A inner) l (Ongoing s) = Some (Ongoing s') -> keeps_exact s s'.
Proof.
    intros nf l s s' H. apply (fold_keeps_exact (fun inner '(P, A) => unify env nf P A inner) l s s'); [| |exact H].
    - intros [P A] s0 s0' _ E. exact (unify_keeps_exact env nf P A s0 s0' E).
    - intros [P A] _. apply unify_keeps_failure.
Qed.

(* A type argument of a supertype, as declared, that is exact for exact type arguments of the subclass:
   invariant, not of any ownership. `class ArrayList<T> : List<T>` has those; `class Holder<T> :
   Consumer<in Box<T>>` doesn't. *)
Definition exact_template_argument (r: EType): bool :=
    match r with
    | TypeArgument Model.invariant o _ => match o with any_ownership => false | _ => true end
    | _ => false
    end.

Lemma template_not_loose: forall sub ys, length ys = length (parameter_ids env sub) ->
    (forall y, In y ys -> is_loose y = false) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> mentions_loosely_bound (bindings_of env sub ys) t = false)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> mentions_loosely_bound (bindings_of env sub ys) r = false).
Proof.
    intros sub ys Hl Hys k. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k -> template_type env sub (RootResolved m c targs) = true ->
        existsb (mentions_loosely_bound (bindings_of env sub ys)) targs = false).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [a [Ha E]].
      pose proof (argument_depth_below m c targs a Ha). rewrite (IHa a ltac:(lia) (Htargs a Ha)) in E. discriminate E. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + rewrite mentions_class. exact (Hroot m c targs Hd Ht).
      + rewrite depth_nullable in Hd. rewrite mentions_nullable, mentions_class. exact (Hroot m c targs ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn]]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hl) Hi) as [y Hy].
        rewrite (mentions_parameter_template _ p bp y (lookup_parameter env wf sub ys i p y Hi Hy)).
        apply Hys. eapply nth_error_In. exact Hy.
      + simpl in Hd |- *. apply IHt; [lia|exact Hn].
Qed.

(* The type arguments of a supertype, for exact type arguments of the subclass, are exact where the
   supertype is declared with exact ones *)
Lemma supertype_arguments_exact: forall e c xs, e <> c -> e <> nothing -> base_type_is_subtype_of env e c = true ->
    length xs = length (parameter_ids env e) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall r, In r (supertype_arguments env e c) -> exact_template_argument r = true) ->
    forall z, In z (parameterized_supertype_arguments env e xs c) -> exact_argument env z = true.
Proof.
    intros e c xs Hne Hn Hb Hl Hxs Hex z Hz.
    destruct (wf_supertypes_are_templates env wf e c Hne Hn Hb) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Hz. apply in_map_iff in Hz. destruct Hz as [r [<- Hr]].
    assert (Hfxs: forall x, In x xs -> argument_in_fragment env x = true).
    { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o nx| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (Hta: forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; apply (argument_in_fragment_is_type_argument env), Hfxs, Hx).
    destruct (template_kind env e r (Ht r Hr)) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
    - destruct (nth_error_same_length _ xs i p (eq_sym Hl) Hi) as [x Hx].
      rewrite (selects env wf e xs p bp i x Hi Hx (Hta x (nth_error_In _ _ Hx))). apply Hxs. eapply nth_error_In. exact Hx.
    - pose proof (Hex _ Hr) as Hexr. simpl in Hexr. destruct v; try discriminate Hexr.
      rewrite (instantiate_template_argument env _ Model.invariant o n Ho (template_shape env e n Hn')).
      assert (Hnl: forall x, In x xs -> is_loose x = false).
      { intros x Hx. pose proof (Hxs x Hx) as E. destruct x as [| | | |[] o' nx| |]; try discriminate E.
        destruct o'; try discriminate E; reflexivity. }
      rewrite (proj1 (template_not_loose e xs Hl Hnl (depth n)) n (le_n _) Hn').
      simpl. destruct o; try discriminate Ho; try discriminate Hexr;
          rewrite (template_type_instance_in_fragment env wf e xs n Hl Hfxs Hn'); reflexivity.
Qed.

Lemma forall2_diag: forall {A: Type} (R: A -> A -> Prop) (l: list A), (forall x, In x l -> R x x) -> Forall2 R l l.
Proof.
    intros A R l H. induction l as [|x l IH]; constructor; [apply H; left; reflexivity|].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma uniform_fuel_list: forall {A: Type} (l: list A) (Q: nat -> A -> Prop),
    (forall f f' x, f <= f' -> Q f x -> Q f' x) -> (forall x, In x l -> exists f, Q f x) ->
    exists f, forall x, In x l -> Q f x.
Proof.
    intros A l Q Hm. induction l as [|x l IH]; intros H; [exists 0; intros _ []|].
    destruct (H x (or_introl eq_refl)) as [f1 H1]. destruct (IH (fun y Hy => H y (or_intror Hy))) as [f2 H2].
    exists (max f1 f2). intros y [<-|Hy]; [apply (Hm f1); [lia|exact H1]|apply (Hm f2); [lia|exact (H2 y Hy)]].
Qed.

(* The type parameters a type mentions, in references to them and as ownership, are among vars, with
   the bounds vars have for them *)
Fixpoint refs_within (vars: list (TypeParameterId * EType)) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => refs_within vars a /\ acc) True arguments
    | Nullable n => refs_within vars n
    | Generic (mkGenericRef _ p bound) | TypeVariable (mkGenericRef _ p bound) => In (p, bound) vars
    | TypeArgument _ o n => (forall q, o = parameter_ownership q -> In q (map fst vars)) /\ refs_within vars n
    | _ => True
    end.

Lemma fold_and_in: forall (Q: EType -> Prop) (l: list EType), fold_right (fun a acc => Q a /\ acc) True l -> forall a, In a l -> Q a.
Proof. intros Q l H. induction l as [|x l IH]; intros a Ha; [destruct Ha|]. destruct H as [Hx H]. destruct Ha as [<-|Ha]; auto. Qed.

Lemma fold_and_map: forall (Q: EType -> Prop) (f: EType -> EType) (l: list EType),
    (forall a, In a l -> Q (f a)) -> fold_right (fun a acc => Q a /\ acc) True (map f l).
Proof. intros Q f l H. induction l as [|x l IH]; [exact I|]. split; [apply H; left; reflexivity|]. apply IH. intros a Ha. apply H. right. exact Ha. Qed.

Lemma refs_to_generic: forall vars t, refs_within vars t -> refs_within vars (to_generic t).
Proof.
    intros vars t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct t as [m c args|n|[gm p bnd]|me msg|v o n|[gm p bnd]|cs]; simpl in H |- *; try exact H.
    - apply fold_and_map. intros a Ha. apply (IH (esize a)); [pose proof (esize_in args a Ha); simpl; lia|reflexivity|].
      exact (fold_and_in _ args H a Ha).
    - apply (IH (esize n)); [simpl; lia|reflexivity|exact H].
    - destruct H as [Ho Hn]. split; [exact Ho|]. apply (IH (esize n)); [simpl; lia|reflexivity|exact Hn].
Qed.

Lemma bound_in_from_refs: forall vars b K t, refs_within vars t ->
    (forall p bound, In (p, bound) vars -> binds_exactly env b K [] p bound = true) ->
    (forall q, In q (map fst vars) -> ownership_bound b (parameter_ownership q) = true) ->
    bound_in env b K [] t = true.
Proof.
    intros vars b K t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H Hp Ho.
    destruct t as [m c args|n|[gm p bnd]|me msg|v o n|[gm p bnd]|cs]; simpl in H |- *; try reflexivity.
    - apply forallb_forall. intros a Ha. apply (IH (esize a)); [pose proof (esize_in args a Ha); simpl; lia|reflexivity| |exact Hp|exact Ho].
      exact (fold_and_in _ args H a Ha).
    - apply (IH (esize n)); [simpl; lia|reflexivity|exact H|exact Hp|exact Ho].
    - exact (Hp p bnd H).
    - destruct H as [Hq Hn]. apply andb_true_iff. split.
      + destruct o as [| | |q]; try reflexivity. exact (Ho q (Hq q eq_refl)).
      + apply (IH (esize n)); [simpl; lia|reflexivity|exact Hn|exact Hp|exact Ho].
Qed.

Lemma lookup_map_vars: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId * EType -> EType) p bound,
    NoDup (map fst l) -> In (p, bound) l -> lookup_binding (map (fun v => (fst v, g v)) l) p = Some (g (p, bound)).
Proof.
    intros l g. induction l as [|[q bq] l IH]; intros p bound Hnd Hin; [destruct Hin|].
    inversion Hnd as [|? ? Hnotin Hnd']. subst. simpl. destruct Hin as [E|Hin].
    - injection E as -> ->. rewrite param_eqb_refl. reflexivity.
    - destruct (param_eqb p q) eqn:E.
      + apply param_eqb_eq in E. subst q. exfalso. apply Hnotin. exact (in_map fst _ _ Hin).
      + exact (IH p bound Hnd' Hin).
Qed.

Lemma lookup_combine_none: forall (ids: list TypeParameterId) (xs: list EType) p, ~ In p ids -> lookup_binding (combine ids xs) p = None.
Proof.
    intros ids. induction ids as [|q ids IH]; intros [|x xs] p H; try reflexivity. simpl.
    destruct (param_eqb p q) eqn:E; [apply param_eqb_eq in E; subst q; exfalso; apply H; left; reflexivity|].
    apply IH. intros Hin. apply H. right. exact Hin.
Qed.

(* What unifying the receiver leaves, and how the object relates to the receiver, as references to
   the class the function is declared in *)
Lemma receiver_and_object: forall n mr c cvars ovars ma ca ys u mo e xs zs n0,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    exists ys' n1,
        length ys' = length cvars /\ length zs = length cvars
        /\ (forall y, In y ys' -> argument_in_fragment env y = true)
        /\ (forall i p bound y, nth_error cvars i = Some (p, bound) -> nth_error ys' i = Some y ->
            lookup_state u p = Some (mkVariableState bound y y true true))
        /\ (forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound bound bottom_type false false))
        /\ wf_states u
        /\ Forall2 (fun z y => unify env n1 y z (Ongoing []) = Some (Ongoing [])) zs ys'.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd bnd bottom_type false (existsb (param_eqb q) (map fst cvars))))
        (cvars ++ ovars)).
    assert (Hs0: for_inference_of (cvars ++ ovars) (map fst cvars) = Ongoing s0) by reflexivity.
    rewrite Hs0 in Hrec.
    rewrite map_app in Hnd.
    assert (Hndc: NoDup (map fst cvars)) by exact (nodup_app_l _ _ Hnd).
    assert (Hcls: forall p bound, In (p, bound) cvars -> existsb (param_eqb p) (map fst cvars) = true).
    { intros p bound Hin. apply existsb_exists. exists p. split; [exact (in_map fst _ _ Hin)|apply param_eqb_refl]. }
    assert (Hown: forall p bound, In (p, bound) ovars -> existsb (param_eqb p) (map fst cvars) = false).
    { intros p bound Hin. apply not_true_iff_false. intros E. apply existsb_exists in E. destruct E as [q [Hq Hpq]].
      apply param_eqb_eq in Hpq. subst q. exact (nodup_app_disjoint _ _ p Hnd Hq (in_map fst _ _ Hin)). }
    assert (Hnd': NoDup (map fst (cvars ++ ovars))) by (rewrite map_app; exact Hnd).
    (* the receiver, as a reference to c, binds the type parameters of c exactly *)
    destruct n as [|n]; [discriminate Hrec|].
    rewrite unify_classes in Hrec.
    destruct (base_type_is_subtype_of env ca c) eqn:Hbca; [|discriminate Hrec].
    destruct (Model.is_subtype_of _ _) eqn:Hmr; [|discriminate Hrec].
    rewrite (class_eqb_false ca nothing Hca) in Hrec. unfold unify_arguments in Hrec.
    set (ys' := if class_eqb ca c then ys else parameterized_supertype_arguments env ca ys c) in Hrec.
    assert (Hys': length ys' = length (parameter_ids env c) /\ forall y, In y ys' -> argument_in_fragment env y = true).
    { unfold ys'. destruct (Class_eq_dec ca c) as [<-|Hne]; [rewrite class_eqb_refl; exact (root_in_fragment env ma ca ys Hfy)|].
      rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env ma ca ys Hfy) as [Hly0 Hys0].
      exact (supertype_arguments_in_fragment env wf ca c ys Hne Hca Hbca Hly0 Hys0). }
    destruct Hys' as [Hly Hys].
    assert (Hl: length ys' = length cvars) by (rewrite Hly, <- Hids, length_map; reflexivity).
    assert (Hfresh: forall p bound, In (p, bound) cvars ->
        lookup_state s0 p = Some (mkVariableState bound bound bottom_type false true) /\ in_fragment env bound = true).
    { intros p bound Hin. split; [|exact (Hbounds p bound (in_or_app _ _ _ (or_introl Hin)))].
      unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_introl Hin))), (Hcls p bound Hin). reflexivity. }
    destruct (capture_arguments env wf n cvars ys' s0 u Hndc Hl Hys Hfresh Hrec) as [Hcap Hoth].
    assert (Hownu: forall p bound, In (p, bound) ovars -> lookup_state u p = Some (mkVariableState bound bound bottom_type false false)).
    { intros p bound Hin.
      assert (Hnin: ~ In p (map fst cvars)) by (intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite (Hoth p Hnin). unfold s0. rewrite (lookup_for_inference _ _ p bound Hnd' (in_or_app _ _ _ (or_intror Hin))).
      rewrite (Hown p bound Hin). reflexivity. }
    (* the variable states are those unify works with *)
    assert (Hwfu: wf_states u).
    { intros p st Hp. destruct (in_dec Nat.eq_dec p (map fst cvars)) as [Hin|Hnin].
      - apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        rewrite (Hcap i p bound y Hi Hy) in Hp. injection Hp as <-. cbn [upper_bound lower_bound is_exact].
        pose proof (argument_in_fragment_no_vars y (Hys y (nth_error_In _ _ Hy))) as Hny.
        split; [exact Hny|]. split; [exact Hny|]. intros E; discriminate E.
      - rewrite (Hoth p Hnin) in Hp. unfold s0 in Hp. destruct (lookup_for_inference_in _ _ p st Hp) as [bound Hin].
        rewrite (lookup_for_inference _ _ p bound Hnd' Hin) in Hp. injection Hp as <-.
        apply in_app_or in Hin as Hin2. destruct Hin2 as [Hin2|Hin2]; [exfalso; apply Hnin; exact (in_map fst _ _ Hin2)|].
        rewrite (Hown p bound Hin2). cbn [upper_bound lower_bound is_exact is_capturable].
        pose proof (Hbounds p bound Hin) as Hfb.
        split; [exact (in_fragment_no_vars bound Hfb)|]. split; [reflexivity|]. intros _. split; [reflexivity|].
        split; [exists 2; apply (below_all env wf [] bound 2 Hfb); lia|]. split; [intros x f _ Ex; exists f; exact Ex|].
        split; [exact (in_fragment_bfrag _ Hfb)|exact (in_fragment_bfrag _ (bottom_in_fragment env wf))]. }
    (* the type arguments of the object as c, assignable to those of the receiver as c *)
    assert (Hfzs: forall z, In z zs -> argument_in_fragment env z = true).
    { intros z Hz. pose proof (Hzx z Hz) as E. destruct z as [| | | |[] o nz| |]; try discriminate E.
      simpl in E |- *. apply andb_true_iff in E. apply E. }
    assert (HfD: in_fragment env (RootResolved mr c ys') = true).
    { change (Nat.eqb (length ys') (length (parameter_ids env c)) && forallb (argument_in_fragment env) ys' = true).
      rewrite Hly, Nat.eqb_refl. apply forallb_forall, Hys. }
    set (k := depth (RootResolved mr c ys')).
    assert (HD: unify env (S k) (RootResolved mr c ys') (RootResolved ma ca ys) (Ongoing []) = Some (Ongoing [])).
    { rewrite unify_classes, Hbca, (mutability_of_class env mr c ys' (map receiver_leaf cvars)), Hmr, (class_eqb_false ca nothing Hca).
      fold ys'. unfold unify_arguments. apply (fold_of_pairs env). apply forall2_diag. intros y Hy.
      apply (proj2 (reflexivity_with_arguments env k)); [exact (Hys y Hy)|].
      pose proof (argument_depth_below mr c ys' y Hy). unfold k. lia. }
    unfold is_assignable_to, empty_unification in Hobj.
    destruct (unify env n0 (RootResolved ma ca ys) (RootResolved mo e xs) (Ongoing [])) as [[w|]|] eqn:Eo; try discriminate Hobj.
    pose proof (proj1 (keeps_states_with_arguments env wf n0) _ _ [] w Hfy Hfo Eo) as ->.
    pose proof (proj1 (transitivity_with_arguments env wf (n0 + S k)) _ _ _ n0 (S k) [] (le_n _) Hfo Hfy HfD Eo HD) as ED.
    replace (n0 + S k) with (S (n0 + k)) in ED by lia.
    rewrite unify_classes in ED.
    destruct (base_type_is_subtype_of env e c) eqn:Hbe; [|discriminate ED].
    match type of ED with context [if Model.is_subtype_of ?x ?y then _ else _] =>
        destruct (Model.is_subtype_of x y); [|discriminate ED] end.
    rewrite (class_eqb_false e nothing He), <- Hzs in ED.
    assert (Hlz: length zs = length ys').
    { rewrite Hly. subst zs. destruct (Class_eq_dec e c) as [<-|Hne].
      - rewrite class_eqb_refl. exact (proj1 (root_in_fragment env mo e xs Hfo)).
      - rewrite (class_eqb_false _ _ Hne). destruct (root_in_fragment env mo e xs Hfo) as [Hlx Hxs].
        exact (proj1 (supertype_arguments_in_fragment env wf e c xs Hne He Hbe Hlx Hxs)). }
    pose proof (pairwise_of_arguments env (n0 + k) ys' zs [] ltac:(lia)
        (fun t a w0 Ht Ha E => proj2 (keeps_states_with_arguments env wf (n0 + k)) t a [] w0 (Hys t Ht) (Hfzs a Ha) E) ED) as Hp.
    exists ys', (n0 + k). split; [exact Hl|]. split; [lia|]. split; [exact Hys|]. split; [exact Hcap|]. split; [exact Hownu|].
    split; [exact Hwfu|]. exact Hp.
Qed.

(*
 * Calling a member function is sound: the function is declared in class c; the receiver is a reference
 * to a class ca below c, whose type arguments, as those of c, are captured by the type parameters of
 * c; the object called on is of a class e below ca, its type arguments as those of c exact (as they
 * are where e declares its supertypes with exact type arguments: supertype_arguments_exact) and
 * within the bounds of the type parameters of c. Inferring the type parameters of the function from
 * the arguments gives them lower and upper bounds, and their final values. Whatever argument is
 * accepted for a parameter fits the parameter with the type parameters of c replaced by the type
 * arguments of the object as c, and those of the function by their final values.
 *)
Theorem member_call_through_subtypes_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is; its type arguments as those of c are exact, and within the bounds *)
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall z, In z zs -> exact_argument env z = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of U p) -> xfrag (final_value_of U p)) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx Hzb
        HPs HAs Hfold Hfinal b Hbdef.
    destruct (receiver_and_object n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu Hp]]]]]]]].
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    (* the variable states unify ends with, with the bounds themselves for the type parameters *)
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (uniform_fuel_list vars (fun f v => unify env f (snd v) (snd v) (Ongoing []) = Some (Ongoing [])))
        as [K0 HK0].
    { intros f f' v Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { intros [p bound] Hin. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs vars); [exact (refs_to_generic vars P (proj2 (HPs P HP)))| |].
      - intros p bound Hin. unfold binds_exactly, b0. rewrite (lookup_map_vars vars _ p bound Hnd' Hin). cbn [snd].
        rewrite (in_fragment_is_gfrag env _ (Hbounds p bound Hin)). unfold respects. pose proof (HK0 (p, bound) Hin) as E0. cbn [snd] in E0. rewrite E0. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (invocation_sound nf Ps As u U b0 K0 Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb0 P HP)) HAs Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify nf _ u U Hfold) as [Hkeep Hkeep2].
    assert (Hfinal': forall p bound, In (p, bound) ovars -> xfrag (final_value_of U p)).
    { intros p bound Hin. apply (Hfinal p bound Hin).
      destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [_ [Hbu Hbl]]]].
      unfold final_value_of, final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    (* the type parameters of the function: their final values, below their bounds *)
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ final_value_of U p = final_value st /\ fits st ref (final_value st)
        /\ exists f, unify env f bound (final_value st) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      pose proof (Hfinal' p bound Hin) as Hff. unfold final_value_of in Hff. rewrite HlU in Hff.
      pose proof (final_value_fits U p st2 ref HwfU HlU He2 Hff) as Hfit.
      exists st2. split; [exact HlU|]. split; [exact He2|]. split; [unfold final_value_of; rewrite HlU; reflexivity|].
      split; [exact Hfit|].
      destruct (HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [Hbs _]]].
      unfold fits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
      destruct (Hbs _ K2 Hff E2) as [f Ef]. cbn [static_upper_bound] in Hst2. rewrite Hst2 in Ef. exists f. exact Ef. }
    (* the type arguments of b, within the bounds *)
    assert (Hlookup: forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ gfrag env x = true
        /\ exists f, unify env f bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. rewrite Hbdef, lookup_app. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (lookup_parameter env wf c zs i p z Hpi Hz).
        destruct (Hzb i p bound z Hi Hz) as [o [x [f [-> Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        exists o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact (in_fragment_is_gfrag env _ Hx)|]. exists f. exact Ef.
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
        assert (Hndo: NoDup (map fst ovars)).
        { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
          inversion H. apply IH. assumption. }
        rewrite (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (final_value_of U (fst v))) p bound Hndo Hin).
        cbn [fst]. exists ref, (final_value_of U p). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (xfrag_gfrag _ (Hfinal' p bound Hin))|].
        destruct (Hfin p bound Hin) as [st [_ [_ [-> [_ Ef]]]]]. exact Ef. }
    destruct (uniform_fuel_list vars (fun f v => forall o x, lookup_binding b (fst v) = Some (TypeArgument Model.invariant o x) ->
        unify env f (snd v) x (Ongoing []) = Some (Ongoing []))) as [K HK].
    { intros f f' v Hle E o x Hx. exact (unify_fuel_monotone env f f' _ _ _ _ Hle (E o x Hx)). }
    { intros [p bound] Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [_ [_ [f Ef]]]]]].
      exists f. intros o' x' Hx'. cbn [fst snd] in Hx' |- *. rewrite Hl' in Hx'. injection Hx' as <- <-. exact Ef. }
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs vars); [exact (refs_to_generic vars P (proj2 (HPs P HP)))| |].
      - intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [Ho [Hx _]]]]].
        unfold binds_exactly. rewrite Hl', Ho, Hx. unfold respects. pose proof (HK (p, bound) Hin o x Hl') as E1. cbn [snd] in E1. rewrite E1. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    destruct (invocation_sound nf Ps As u U b K Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb P HP)) HAs Hfold) as [_ Hsound].
    (* the type arguments satisfy the variable states unify ends with *)
    apply Hsound. intros p o x Hpb.
    assert (Hin: exists bound, In (p, bound) vars).
    { rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of U q)) p _ Hpb) as [_ Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        exists bound. apply in_or_app. right. exact Hin. }
    destruct Hin as [bound Hin]. unfold vars in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    - (* a type parameter of c: the type argument of the object, captured by that of the receiver *)
      destruct (In_nth_error _ _ Hin) as [i Hi].
      assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
      destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
      destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
      rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz) in Hpb. injection Hpb as ->.
      pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [_ Hfx].
      split; [exact (in_fragment_xfrag _ Hfx)|]. exists (mkVariableState bound y y true true).
      split; [exact (Hkeep p _ (Hcap i p bound y Hi Hy) eq_refl)|].
      pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy2.
      destruct y as [| | | |vb ob X| |]; try discriminate Hfy2.
      unfold fits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n1. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hfy2|]. split; [exact Hfx|]. apply (unify_fuel_monotone env n1); [lia|].
      exact (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy).
    - (* a type parameter of the function: its final value *)
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None) in Hpb.
      destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of U q)) p _ Hpb) as [Ea _].
      injection Ea as Eo2 Ex2. subst o x.
      destruct (Hfin p bound Hin) as [st [HlU [_ [Hfv [Hfit _]]]]].
      split; [exact (Hfinal' p bound Hin)|]. exists st. split; [exact HlU|]. rewrite Hfv. exact Hfit.
Qed.

(* The same, where the receiver and the object are of the class the function is declared in *)
Theorem member_call_with_type_parameters_sound: forall n mr c cvars ovars ma ys u mo xs n0 Ps As nf U,
    c <> nothing -> map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma c ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma c ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is, of exact type arguments within the bounds *)
    length xs = length (parameter_ids env c) -> (forall x, In x xs -> exact_argument env x = true) ->
    (forall i p bound z, nth_error cvars i = Some (p, bound) -> nth_error xs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    is_assignable_to env n0 (RootResolved mo c xs) (RootResolved ma c ys) = Some true ->
    (* the parameters and the arguments, accepted in turn *)
    (forall P, In P Ps -> ifrag env P = true /\ refs_within (cvars ++ ovars) P) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values of the type parameters of the function, which are bounds, are among the types
       variables are replaced with *)
    (forall p bound, In (p, bound) ovars -> bfrag (final_value_of U p) -> xfrag (final_value_of U p)) ->
    forall b, b = bindings_of env c xs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ys u mo xs n0 Ps As nf U Hc Hids Hnd Hbounds Hfy Hrec Hlx Hxs Hxb Hobj HPs HAs Hfold Hfinal
        b Hbdef.
    assert (Hfo: in_fragment env (RootResolved mo c xs) = true).
    { change (Nat.eqb (length xs) (length (parameter_ids env c)) && forallb (argument_in_fragment env) xs = true).
      rewrite Hlx, Nat.eqb_refl. apply forallb_forall. intros x Hx. pose proof (Hxs x Hx) as E.
      destruct x as [| | | |[] o nx| |]; try discriminate E. simpl in E |- *. apply andb_true_iff in E. apply E. }
    exact (member_call_through_subtypes_sound n mr c cvars ovars ma c ys u mo c xs xs n0 Ps As nf U Hc Hc Hc Hids Hnd Hbounds
        Hfy Hrec Hfo Hobj ltac:(rewrite class_eqb_refl; reflexivity) Hxs Hxb HPs HAs Hfold Hfinal b Hbdef).
Qed.

End Constraints.

(* The class types of Transitivity.v are types to replace the variables with, as Constraints needs them *)
Lemma classes_as_replacements: forall env,
    (forall x, in_fragment env x = true -> gfrag env x = true)
    /\ (forall x, in_fragment env x = true -> exists n, unify env n x x (Ongoing []) = Some (Ongoing [])).
Proof.
    intros env. split; [exact (in_fragment_is_gfrag env)|].
    intros x Hx. exists (depth x). exact (proj1 (reflexivity_with_arguments env (depth x)) x [] Hx (le_n _)).
Qed.

(* The types without type variables are bounds, as Constraints needs them, where intersect and
   closestCommonSupertypeWith make up none *)
Lemma no_vars_as_bounds: forall env,
    (forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true) ->
    (forall a b, no_vars a = true -> no_vars b = true -> no_vars (closest_common_supertype_with env a b) = true) ->
    (forall x, in_fragment env x = true -> no_vars x = true)
    /\ (forall a b, no_vars a = true -> in_fragment env b = true -> no_vars (intersect env a b) = true)
    /\ (forall a b, no_vars a = true -> in_fragment env b = true -> no_vars (closest_common_supertype_with env a b) = true).
Proof.
    intros env Hi Hs. split; [exact (in_fragment_no_vars env)|].
    split; intros a b Ha Hb; [apply Hi|apply Hs]; [exact Ha|exact (in_fragment_no_vars env b Hb)|exact Ha|exact (in_fragment_no_vars env b Hb)].
Qed.

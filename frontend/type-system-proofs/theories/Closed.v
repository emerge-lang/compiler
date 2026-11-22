From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Transitivity.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Unify on closed types                                                                           *)
(*                                                                                                *)
(* On types without type variables (no_vars), unify never touches the variable states: it answers  *)
(* the same from any states, and with those states (States.unify_free). So what it decides of such *)
(* types is a closed question, is_assignable_to, and the theorems about them need neither states   *)
(* nor fuel in their statements: a type is assignable to another (assignable: some fuel accepts),  *)
(* unify never rejects it (never_fails: no fuel does), unify answers (answers: some fuel does).     *)
(* This file has that vocabulary, the facts about fuel once (what is accepted is never rejected,   *)
(* what is never rejected and answered is accepted, one fuel serves finitely many questions), and  *)
(* the closed forms of the searches unify runs over components: a fold that stops at the first     *)
(* component that is not accepted (closed_fold), a search for the first that is (closed_first),    *)
(* which union_flipped_unify, intersection_flipped_unify, union_body and intersection_body are.    *)
(* Whatever is stated about closed types above this file is stated in these terms.                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* The answer of a unification: accepted, rejected, or none *)
Definition verdict (u: option Unification): option bool :=
    option_map (fun u => match u with Ongoing _ => true | Failed => false end) u.

(* The answer, as a unification that started in states s ends *)
Definition with_states (s: VariableStates) (r: option bool): option Unification :=
    match r with Some true => Some (Ongoing s) | Some false => Some Failed | None => None end.

Lemma verdict_with_states: forall s answer, verdict (with_states s answer) = answer.
Proof. intros s [[]|]; reflexivity. Qed.

(* A fold over components that stops at the first one not accepted *)
Fixpoint closed_fold (f: EType -> option bool) (l: list EType): option bool :=
    match l with
    | [] => Some true
    | x :: l' => match f x with Some true => closed_fold f l' | r => r end
    end.

(* A search for the first component accepted; rejected where none is *)
Fixpoint closed_first (f: EType -> option bool) (l: list EType): option bool :=
    match l with
    | [] => Some false
    | x :: l' => match f x with Some false => closed_first f l' | r => r end
    end.

Lemma closed_fold_true: forall f l, closed_fold f l = Some true <-> forall x, In x l -> f x = Some true.
Proof.
    intros f l. induction l as [|x l IH]; simpl; [split; [intros _ x []|reflexivity]|].
    destruct (f x) as [[]|] eqn:E.
    - rewrite IH. split; [intros H y [<-|Hy]; [exact E|exact (H y Hy)]|intros H y Hy; apply H; right; exact Hy].
    - split; [discriminate|intros H; rewrite (H x (or_introl eq_refl)) in E; discriminate E].
    - split; [discriminate|intros H; rewrite (H x (or_introl eq_refl)) in E; discriminate E].
Qed.

Lemma closed_fold_not_false: forall f l, (forall x, In x l -> f x <> Some false) -> closed_fold f l <> Some false.
Proof.
    intros f l H. induction l as [|x l IH]; simpl; [discriminate|]. destruct (f x) as [[]|] eqn:E; [|exfalso; exact (H x (or_introl eq_refl) E)|discriminate].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma closed_fold_some: forall f l, (forall x, In x l -> f x <> None) -> closed_fold f l <> None.
Proof.
    intros f l H. induction l as [|x l IH]; simpl; [discriminate|]. destruct (f x) as [[]|] eqn:E; [|discriminate|exfalso; exact (H x (or_introl eq_refl) E)].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma closed_first_true: forall f l, closed_first f l = Some true -> exists x, In x l /\ f x = Some true.
Proof.
    intros f l. induction l as [|x l IH]; simpl; [discriminate|]. destruct (f x) as [[]|] eqn:E; intros H; try discriminate H.
    - exists x. split; [left; reflexivity|exact E].
    - destruct (IH H) as [y [Hy Hf]]. exists y. split; [right; exact Hy|exact Hf].
Qed.

Lemma closed_first_false: forall f l, closed_first f l = Some false -> forall x, In x l -> f x = Some false.
Proof.
    intros f l. induction l as [|x l IH]; simpl; [intros _ x []|]. destruct (f x) as [[]|] eqn:E; intros H y Hy; try discriminate H.
    destruct Hy as [<-|Hy]; [exact E|exact (IH H y Hy)].
Qed.

Lemma closed_first_not_false: forall f l x, In x l -> f x <> Some false -> closed_first f l <> Some false.
Proof.
    intros f l x Hx H. induction l as [|y l IH]; [destruct Hx|]. simpl. destruct (f y) as [[]|] eqn:E; try discriminate.
    destruct Hx as [<-|Hx]; [exfalso; exact (H E)|exact (IH Hx)].
Qed.

Lemma closed_first_some: forall f l, (forall x, In x l -> f x <> None) -> closed_first f l <> None.
Proof.
    intros f l H. induction l as [|x l IH]; simpl; [discriminate|]. destruct (f x) as [[]|] eqn:E; [discriminate| |exfalso; exact (H x (or_introl eq_refl) E)].
    apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* Where every component answers and one is accepted, the search accepts *)
Lemma closed_first_found: forall f l x, (forall y, In y l -> f y <> None) -> In x l -> f x = Some true -> closed_first f l = Some true.
Proof.
    intros f l x Hall Hx H. induction l as [|y l IH]; [destruct Hx|]. simpl. destruct (f y) as [[]|] eqn:E; [reflexivity| |].
    - destruct Hx as [<-|Hx]; [rewrite H in E; discriminate E|]. apply IH; [intros z Hz; apply Hall; right; exact Hz|exact Hx].
    - exfalso. exact (Hall y (or_introl eq_refl) E).
Qed.

Lemma closed_fold_mono: forall (f0 f1: EType -> option bool) l, (forall x, In x l -> f0 x = Some true -> f1 x = Some true) ->
    closed_fold f0 l = Some true -> closed_fold f1 l = Some true.
Proof. intros f0 f1 l H H0. apply closed_fold_true. intros x Hx. exact (H x Hx (proj1 (closed_fold_true f0 l) H0 x Hx)). Qed.

Section ClosedUnify.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* x is assignable to y: some fuel accepts *)
Definition assignable (x y: EType): Prop := exists n, is_assignable_to env n x y = Some true.

(* unify never rejects a for t: no fuel does *)
Definition never_fails (t a: EType): Prop := forall n, is_assignable_to env n a t <> Some false.

(* unify answers whether a is assignable to t: some fuel does *)
Definition answers (t a: EType): Prop := exists n, is_assignable_to env n a t <> None.

(* The closed question, of any fuel: a step of unify *)
Lemma assignable_step: forall n x y, is_assignable_to env (S n) x y = verdict (unify_step env (unify env n) y x []).
Proof. reflexivity. Qed.

Lemma assignable_none: forall x y, is_assignable_to env 0 x y = None.
Proof. reflexivity. Qed.

(* On closed types, unify answers the same from any states, with those states *)
Lemma closed_unify: forall n t a s, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = with_states s (is_assignable_to env n a t).
Proof.
    intros n t a s Ht Ha. unfold is_assignable_to, empty_unification.
    destruct (unify env n t a (Ongoing [])) as [[s'|]|] eqn:E; cbn [verdict with_states option_map].
    - exact (unify_free env wf n t a [] s _ Ht Ha E).
    - exact (unify_free env wf n t a [] s _ Ht Ha E).
    - destruct (unify env n t a (Ongoing s)) as [u|] eqn:E'; [|reflexivity].
      rewrite (unify_free env wf n t a s [] u Ht Ha E') in E. discriminate E.
Qed.

Lemma closed_fuel_monotone: forall n n' x y answer, n <= n' -> is_assignable_to env n x y = Some answer -> is_assignable_to env n' x y = Some answer.
Proof.
    intros n n' x y answer Hle H. unfold is_assignable_to, empty_unification in *.
    destruct (unify env n y x (Ongoing [])) as [u|] eqn:E; [|discriminate H].
    rewrite (unify_fuel_monotone env n n' _ _ _ u Hle E). exact H.
Qed.

Lemma assignable_mono: forall n n' x y, n <= n' -> is_assignable_to env n x y = Some true -> is_assignable_to env n' x y = Some true.
Proof. intros n n' x y Hle H. exact (closed_fuel_monotone n n' x y true Hle H). Qed.

Lemma answers_mono: forall n n' x y, n <= n' -> is_assignable_to env n x y <> None -> is_assignable_to env n' x y <> None.
Proof.
    intros n n' x y Hle H E. destruct (is_assignable_to env n x y) as [r|] eqn:E0; [|exact (H eq_refl)].
    rewrite (closed_fuel_monotone n n' x y r Hle E0) in E. discriminate E.
Qed.

(* One fuel for all of finitely many questions, where each has one of its own *)
Lemma fuel_for_all: forall (W: nat -> EType -> Prop) (l: list EType), (forall n n' x, n <= n' -> W n x -> W n' x) ->
    (forall x, In x l -> exists n, W n x) -> exists n, forall x, In x l -> W n x.
Proof.
    intros W l Hmono H. induction l as [|x l IH]; [exists 0; intros y []|].
    destruct (H x (or_introl eq_refl)) as [n0 H0]. destruct IH as [n1 H1]; [intros y Hy; apply H; right; exact Hy|].
    exists (max n0 n1). intros y [<-|Hy]; [apply (Hmono n0); [lia|exact H0]|apply (Hmono n1); [lia|exact (H1 y Hy)]].
Qed.

(* What is accepted is never rejected *)
Lemma assignable_never_fails: forall x y, assignable x y -> never_fails y x.
Proof.
    intros x y [n H] n' E. destruct (Nat.le_ge_cases n n') as [Hle|Hle].
    - rewrite (assignable_mono n n' x y Hle H) in E. discriminate E.
    - rewrite (closed_fuel_monotone n' n x y false Hle E) in H. discriminate H.
Qed.

(* What is never rejected and answered is accepted *)
Lemma never_fails_answers: forall x y, never_fails y x -> answers y x -> assignable x y.
Proof.
    intros x y Hnf [n Ha]. exists n. destruct (is_assignable_to env n x y) as [[]|] eqn:E; [reflexivity|exact (False_ind _ (Hnf n E))|exact (False_ind _ (Ha eq_refl))].
Qed.

Lemma assignable_answers: forall x y, assignable x y -> answers y x.
Proof. intros x y [n H]. exists n. rewrite H. discriminate. Qed.

(* never_fails as Generics.v states it, with states *)
Lemma never_fails_states: forall t a, no_vars t = true -> no_vars a = true ->
    never_fails t a <-> forall n s, unify env n t a (Ongoing s) <> Some Failed.
Proof.
    intros t a Ht Ha. split.
    - intros H n s E. rewrite (closed_unify n t a s Ht Ha) in E. destruct (is_assignable_to env n a t) as [[]|] eqn:E'; try discriminate E. exact (H n E').
    - intros H n E. apply (H n []). rewrite (closed_unify n t a [] Ht Ha), E. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The searches over components, closed                                                            *)
(* ---------------------------------------------------------------------------------------------- *)

(* A fold of unifications with the target, over closed components *)
Lemma fold_closed_assignees: forall n t us s, no_vars t = true -> forallb no_vars us = true ->
    fold_unify (fun inner C => unify env n t C inner) us (Ongoing s) = with_states s (closed_fold (fun C => is_assignable_to env n C t) us).
Proof.
    intros n t us s Ht Hus. induction us as [|C us IH]; [reflexivity|]. simpl in Hus |- *. apply andb_true_iff in Hus.
    rewrite (closed_unify n t C s Ht (proj1 Hus)). destruct (is_assignable_to env n C t) as [[]|]; cbn [with_states];
        [exact (IH (proj2 Hus))|apply fold_unify_stays_failed_assignee|reflexivity].
Qed.

(* ... and of the assignee with closed components as the targets *)
Lemma fold_closed_targets: forall n a cs s, no_vars a = true -> forallb no_vars cs = true ->
    fold_unify (fun inner C => unify env n C a inner) cs (Ongoing s) = with_states s (closed_fold (fun C => is_assignable_to env n a C) cs).
Proof.
    intros n a cs s Ha Hcs. induction cs as [|C cs IH]; [reflexivity|]. simpl in Hcs |- *. apply andb_true_iff in Hcs.
    rewrite (closed_unify n C a s (proj1 Hcs) Ha). destruct (is_assignable_to env n a C) as [[]|]; cbn [with_states];
        [exact (IH (proj2 Hcs))|apply fold_unify_stays_failed|reflexivity].
Qed.

Lemma find_first_closed: forall (f: EType -> option bool) (l: list EType) s,
    match find_first (fun C => with_states s (f C)) l with Some (Some _) => Some true | Some None => Some false | None => None end
    = closed_first f l.
Proof.
    intros f l s. induction l as [|x l IH]; [reflexivity|]. simpl. destruct (f x) as [[]|]; cbn [with_states]; [reflexivity|exact IH|reflexivity].
Qed.

Lemma union_flipped_closed: forall n t us s, no_vars t = true -> forallb no_vars us = true ->
    union_flipped_unify (unify env n) t us s = with_states s (closed_fold (fun C => is_assignable_to env n C t) us).
Proof. intros n t us s Ht Hus. exact (fold_closed_assignees n t us s Ht Hus). Qed.

Lemma intersection_flipped_closed: forall n t cs s, no_vars t = true -> forallb no_vars cs = true ->
    verdict (intersection_flipped_unify (unify env n) t cs s) = closed_first (fun C => is_assignable_to env n C t) cs.
Proof.
    intros n t cs s Ht Hcs. unfold intersection_flipped_unify.
    rewrite forallb_forall in Hcs.
    assert (E: find_first (fun C => unify env n t C (Ongoing s)) cs = find_first (fun C => with_states s (is_assignable_to env n C t)) cs).
    { induction cs as [|C cs IH]; [reflexivity|]. simpl. rewrite (closed_unify n t C s Ht (Hcs C (or_introl eq_refl))).
      destruct (is_assignable_to env n C t) as [[]|]; cbn [with_states]; [reflexivity| |reflexivity]. apply IH. intros C' Hc. apply Hcs. right. exact Hc. }
    rewrite E. clear E. etransitivity; [|apply (find_first_closed (fun C => is_assignable_to env n C t) cs s)]. cbn beta.
    destruct (find_first _ cs) as [[[x s']|]|]; reflexivity.
Qed.

Lemma union_body_closed: forall n us a s, forallb no_vars us = true -> no_vars a = true ->
    verdict (union_body (unify env n) us a s) = closed_first (fun C => is_assignable_to env n a C) us.
Proof.
    intros n us a s Hus Ha. unfold union_body. destruct (no_vars_filter us Hus) as [Hvar Hnonvar]. cbn zeta. rewrite Hvar, Hnonvar, app_nil_r.
    rewrite forallb_forall in Hus.
    assert (E: find_first (fun C => unify env n C a (Ongoing s)) us = find_first (fun C => with_states s (is_assignable_to env n a C)) us).
    { clear Hvar Hnonvar. induction us as [|C us IH]; [reflexivity|]. simpl. rewrite (closed_unify n C a s (Hus C (or_introl eq_refl)) Ha).
      destruct (is_assignable_to env n a C) as [[]|]; cbn [with_states]; [reflexivity| |reflexivity]. apply IH. intros C' Hc. apply Hus. right. exact Hc. }
    rewrite E. clear E. etransitivity; [|apply (find_first_closed (fun C => is_assignable_to env n a C) us s)]. cbn beta.
    destruct (find_first _ us) as [[[x s']|]|]; reflexivity.
Qed.

(* An intersection as the target takes the assignee with every component: the fold over its components, which
   are no type variables; the covering component found after it is the first, as every one was accepted *)
Lemma intersection_body_closed: forall n cs a s, forallb no_vars cs = true -> no_vars a = true ->
    verdict (intersection_body env (unify env n) cs a s) = closed_fold (fun C => is_assignable_to env n a C) cs.
Proof.
    intros n cs a s Hcs Ha. unfold intersection_body. destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar]. cbn zeta. rewrite Hvar, Hnonvar.
    rewrite (fold_closed_targets n a cs s Ha Hcs).
    destruct (closed_fold (fun C => is_assignable_to env n a C) cs) as [[]|] eqn:F; cbn [with_states]; [|reflexivity|reflexivity].
    rewrite forallb_forall in Hcs. pose proof (proj1 (closed_fold_true _ cs) F) as Hall.
    destruct cs as [|C cs']; [reflexivity|].
    cbn [find_first]. rewrite (closed_unify n C a s (Hcs C (or_introl eq_refl)) Ha), (Hall C (or_introl eq_refl)). reflexivity.
Qed.

End ClosedUnify.

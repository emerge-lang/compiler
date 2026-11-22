From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Closed.
From EmergeTypeSystem Require Import Generics.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* The rules of unify on closed types, one by one                                                   *)
(*                                                                                                *)
(* A step of unify on a pair of closed types is one of a few rules, each a closed search over       *)
(* components (Closed.v): a union assignee is taken where each component is (closed_fold), a union  *)
(* target takes a value with the first component that does (closed_first), an intersection target  *)
(* takes a value where each component does, an intersection assignee is taken by the first          *)
(* component that is, a nullable target takes a value where what it wraps takes it without null,   *)
(* and a target that isn't nullable rejects a possibly null value. Which rule applies depends on    *)
(* the shapes of the two types only, never on a fragment: so each rule is stated here once, for     *)
(* all the shapes it applies to, as the step of unify it is (..._step) and in the three flavours    *)
(* the theorems need: what is accepted (assignable), what is never rejected (never_fails), what is  *)
(* answered (answers). A proof about a fragment then reasons by rule, not by pair of shapes.        *)
(* ---------------------------------------------------------------------------------------------- *)

Section Rules.

Variable env: Environment.
Hypothesis wf: wellformed env.

Let assignable := Closed.assignable env.
Let never_fails := Closed.never_fails env.
Let answers := Closed.answers env.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the assignee, to a target that is no intersection: taken where each component is     *)
(* ---------------------------------------------------------------------------------------------- *)

Definition takes_unions (t: EType): Prop := match t with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end.

Lemma union_assignee_step: forall n t us, no_vars t = true -> forallb no_vars us = true -> takes_unions t ->
    is_assignable_to env (S n) (Union us) t = closed_fold (fun C => is_assignable_to env n C t) us.
Proof.
    intros n t us Ht Hus Hs. rewrite assignable_step. destruct t as [| |[]| | | | |]; try contradiction;
        cbn [unify_step unify_root_resolved unify_nullable unify_generic unify_union]; rewrite (union_flipped_closed env wf n _ us [] Ht Hus);
        apply verdict_with_states.
Qed.

Lemma union_assignee_components: forall t us, no_vars t = true -> forallb no_vars us = true -> takes_unions t ->
    assignable (Union us) t -> forall C, In C us -> assignable C t.
Proof.
    intros t us Ht Hus Hs [n H] C Hc. destruct n as [|n]; [discriminate H|]. rewrite (union_assignee_step n t us Ht Hus Hs) in H.
    exists n. exact (proj1 (closed_fold_true _ us) H C Hc).
Qed.

Lemma union_assignee_taken: forall t us, no_vars t = true -> forallb no_vars us = true -> takes_unions t ->
    (forall C, In C us -> assignable C t) -> assignable (Union us) t.
Proof.
    intros t us Ht Hus Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n C t = Some true) us) as [n Hn].
    { intros n n' C Hle. exact (assignable_mono env n n' C t Hle). }
    { exact H. }
    exists (S n). rewrite (union_assignee_step n t us Ht Hus Hs). apply closed_fold_true. exact Hn.
Qed.

Lemma union_assignee_never_fails: forall t us, no_vars t = true -> forallb no_vars us = true -> takes_unions t ->
    (forall C, In C us -> never_fails t C) -> never_fails t (Union us).
Proof.
    intros t us Ht Hus Hs H n E. destruct n as [|n]; [discriminate E|]. rewrite (union_assignee_step n t us Ht Hus Hs) in E.
    exact (closed_fold_not_false _ us (fun C Hc => H C Hc n) E).
Qed.

Lemma union_assignee_answers: forall t us, no_vars t = true -> forallb no_vars us = true -> takes_unions t ->
    (forall C, In C us -> answers t C) -> answers t (Union us).
Proof.
    intros t us Ht Hus Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n C t <> None) us) as [n Hn].
    { intros n n' C Hle. exact (answers_mono env n n' C t Hle). }
    { exact H. }
    exists (S n). rewrite (union_assignee_step n t us Ht Hus Hs). exact (closed_fold_some _ us Hn).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the target, of a class type, a reference, or a nullable type: the first component    *)
(* that takes it                                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

Definition searched_in_unions (a: EType): Prop := match a with RootResolved _ _ _ | Nullable _ | Generic _ => True | _ => False end.

Lemma union_target_step: forall n us a, forallb no_vars us = true -> no_vars a = true -> searched_in_unions a ->
    is_assignable_to env (S n) a (Union us) = closed_first (fun C => is_assignable_to env n a C) us.
Proof.
    intros n us a Hus Ha Hs. rewrite assignable_step. destruct a as [| | | | | | |]; try contradiction;
        cbn [unify_step unify_union]; exact (union_body_closed env wf n us _ [] Hus Ha).
Qed.

Lemma union_target_component: forall us a, forallb no_vars us = true -> no_vars a = true -> searched_in_unions a ->
    assignable a (Union us) -> exists C, In C us /\ assignable a C.
Proof.
    intros us a Hus Ha Hs [n H]. destruct n as [|n]; [discriminate H|]. rewrite (union_target_step n us a Hus Ha Hs) in H.
    destruct (closed_first_true _ us H) as [C [Hc HC]]. exists C. split; [exact Hc|exists n; exact HC].
Qed.

(* ... where every component answers *)
Lemma union_target_takes: forall us a C, forallb no_vars us = true -> no_vars a = true -> searched_in_unions a ->
    (forall C', In C' us -> answers C' a) -> In C us -> assignable a C -> assignable a (Union us).
Proof.
    intros us a C Hus Ha Hs Hall Hc [n H]. destruct (fuel_for_all (fun n C' => is_assignable_to env n a C' <> None) us) as [n0 Hn0].
    { intros n1 n2 C' Hle. exact (answers_mono env n1 n2 a C' Hle). }
    { exact Hall. }
    exists (S (max n n0)). rewrite (union_target_step (max n n0) us a Hus Ha Hs).
    apply (closed_first_found _ us C); [intros C' Hc'; apply (answers_mono env n0); [lia|exact (Hn0 C' Hc')]|exact Hc|].
    apply (assignable_mono env n); [lia|exact H].
Qed.

Lemma union_target_never_fails: forall us a C, forallb no_vars us = true -> no_vars a = true -> searched_in_unions a ->
    In C us -> never_fails C a -> never_fails (Union us) a.
Proof.
    intros us a C Hus Ha Hs Hc H n E. destruct n as [|n]; [discriminate E|]. rewrite (union_target_step n us a Hus Ha Hs) in E.
    exact (closed_first_not_false _ us C Hc (H n) E).
Qed.

Lemma union_target_answers: forall us a, forallb no_vars us = true -> no_vars a = true -> searched_in_unions a ->
    (forall C, In C us -> answers C a) -> answers (Union us) a.
Proof.
    intros us a Hus Ha Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n a C <> None) us) as [n Hn].
    { intros n n' C Hle. exact (answers_mono env n n' a C Hle). }
    { exact H. }
    exists (S n). rewrite (union_target_step n us a Hus Ha Hs). exact (closed_first_some _ us Hn).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the target, of an intersection: a component of the intersection below the whole      *)
(* union, or else a component of the union that takes the intersection                             *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma union_intersection_step: forall n us cs, forallb no_vars us = true -> forallb no_vars cs = true ->
    is_assignable_to env (S n) (Intersection cs) (Union us)
    = match closed_first (fun C => is_assignable_to env n C (Union us)) cs with
      | Some false => closed_first (fun C => is_assignable_to env n (Intersection cs) C) us
      | r => r
      end.
Proof.
    intros n us cs Hus Hcs. rewrite assignable_step. cbn [unify_step unify_union].
    rewrite <- (intersection_flipped_closed env wf n (Union us) cs [] Hus Hcs), <- (union_body_closed env wf n us (Intersection cs) [] Hus Hcs).
    destruct (intersection_flipped_unify (unify env n) (Union us) cs []) as [[s'|]|]; reflexivity.
Qed.

Lemma intersection_below_union: forall us cs, forallb no_vars us = true -> forallb no_vars cs = true ->
    assignable (Intersection cs) (Union us) ->
    (exists C, In C cs /\ assignable C (Union us)) \/ (exists y, In y us /\ assignable (Intersection cs) y).
Proof.
    intros us cs Hus Hcs [n H]. destruct n as [|n]; [discriminate H|]. rewrite (union_intersection_step n us cs Hus Hcs) in H.
    destruct (closed_first (fun C => is_assignable_to env n C (Union us)) cs) as [[]|] eqn:E; try discriminate H.
    - left. destruct (closed_first_true _ cs E) as [C [Hc HC]]. exists C. split; [exact Hc|exists n; exact HC].
    - right. destruct (closed_first_true _ us H) as [y [Hy Hu]]. exists y. split; [exact Hy|exists n; exact Hu].
Qed.

(* The union takes the intersection where a component of it is below the union, and the components answer *)
Lemma intersection_below_union_by_component: forall us cs C, forallb no_vars us = true -> forallb no_vars cs = true ->
    (forall C', In C' cs -> answers (Union us) C') -> In C cs -> assignable C (Union us) -> assignable (Intersection cs) (Union us).
Proof.
    intros us cs C Hus Hcs Hall Hc [n H]. destruct (fuel_for_all (fun n C' => is_assignable_to env n C' (Union us) <> None) cs) as [n0 Hn0].
    { intros n1 n2 C' Hle. exact (answers_mono env n1 n2 C' (Union us) Hle). }
    { exact Hall. }
    exists (S (max n n0)). rewrite (union_intersection_step (max n n0) us cs Hus Hcs).
    rewrite (closed_first_found _ cs C); [reflexivity|intros C' Hc'; apply (answers_mono env n0); [lia|exact (Hn0 C' Hc')]|exact Hc|].
    apply (assignable_mono env n); [lia|exact H].
Qed.

(* The union never rejects the intersection where one of the intersection's components is never rejected by it *)
Lemma union_target_intersection_never_fails: forall us cs C, forallb no_vars us = true -> forallb no_vars cs = true -> In C cs ->
    never_fails (Union us) C -> never_fails (Union us) (Intersection cs).
Proof.
    intros us cs C Hus Hcs Hc H n E. destruct n as [|n]; [discriminate E|]. rewrite (union_intersection_step n us cs Hus Hcs) in E.
    destruct (closed_first (fun C' => is_assignable_to env n C' (Union us)) cs) as [[]|] eqn:F; try discriminate E.
    exact (closed_first_not_false _ cs C Hc (H n) F).
Qed.

(* ... or where one of the union's components never rejects the intersection *)
Lemma union_component_intersection_never_fails: forall us cs C, forallb no_vars us = true -> forallb no_vars cs = true -> In C us ->
    never_fails C (Intersection cs) -> never_fails (Union us) (Intersection cs).
Proof.
    intros us cs C Hus Hcs Hc H n E. destruct n as [|n]; [discriminate E|]. rewrite (union_intersection_step n us cs Hus Hcs) in E.
    destruct (closed_first (fun C' => is_assignable_to env n C' (Union us)) cs) as [[]|]; [discriminate E| |discriminate E].
    exact (closed_first_not_false _ us C Hc (H n) E).
Qed.

Lemma union_target_intersection_answers: forall us cs, forallb no_vars us = true -> forallb no_vars cs = true ->
    (forall C, In C cs -> answers (Union us) C) -> (forall C, In C us -> answers C (Intersection cs)) -> answers (Union us) (Intersection cs).
Proof.
    intros us cs Hus Hcs Hfirst Hthen.
    destruct (fuel_for_all (fun n C => is_assignable_to env n C (Union us) <> None) cs) as [n0 Hn0].
    { intros n n' C Hle. exact (answers_mono env n n' C (Union us) Hle). }
    { exact Hfirst. }
    destruct (fuel_for_all (fun n C => is_assignable_to env n (Intersection cs) C <> None) us) as [n1 Hn1].
    { intros n n' C Hle. exact (answers_mono env n n' (Intersection cs) C Hle). }
    { exact Hthen. }
    exists (S (max n0 n1)). rewrite (union_intersection_step (max n0 n1) us cs Hus Hcs).
    destruct (closed_first (fun C => is_assignable_to env (max n0 n1) C (Union us)) cs) as [[]|] eqn:F; [discriminate| |].
    - apply closed_first_some. intros C Hc. apply (answers_mono env n1); [lia|exact (Hn1 C Hc)].
    - exfalso. apply (closed_first_some (fun C => is_assignable_to env (max n0 n1) C (Union us)) cs); [|exact F].
      intros C Hc. apply (answers_mono env n0); [lia|exact (Hn0 C Hc)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* An intersection as the target: takes a value where each of its components does                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma intersection_target_step: forall n cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    is_assignable_to env (S n) a (Intersection cs) = closed_fold (fun C => is_assignable_to env n a C) cs.
Proof.
    intros n cs a Hcs Ha Hs. rewrite <- (intersection_body_closed env wf n cs a [] Hcs Ha). unfold is_assignable_to, empty_unification.
    rewrite (inter_body env n cs a [] _ Hs eq_refl). reflexivity.
Qed.

Lemma intersection_target_components: forall cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    assignable a (Intersection cs) -> forall C, In C cs -> assignable a C.
Proof.
    intros cs a Hcs Ha Hs [n H] C Hc. destruct n as [|n]; [discriminate H|]. rewrite (intersection_target_step n cs a Hcs Ha Hs) in H.
    exists n. exact (proj1 (closed_fold_true _ cs) H C Hc).
Qed.

Lemma intersection_target_takes: forall cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    (forall C, In C cs -> assignable a C) -> assignable a (Intersection cs).
Proof.
    intros cs a Hcs Ha Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n a C = Some true) cs) as [n Hn].
    { intros n n' C Hle. exact (assignable_mono env n n' a C Hle). }
    { exact H. }
    exists (S n). rewrite (intersection_target_step n cs a Hcs Ha Hs). apply closed_fold_true. exact Hn.
Qed.

Lemma intersection_target_never_fails: forall cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    (forall C, In C cs -> never_fails C a) -> never_fails (Intersection cs) a.
Proof.
    intros cs a Hcs Ha Hs H n E. destruct n as [|n]; [discriminate E|]. rewrite (intersection_target_step n cs a Hcs Ha Hs) in E.
    exact (closed_fold_not_false _ cs (fun C Hc => H C Hc n) E).
Qed.

Lemma intersection_target_answers: forall cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    (forall C, In C cs -> answers C a) -> answers (Intersection cs) a.
Proof.
    intros cs a Hcs Ha Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n a C <> None) cs) as [n Hn].
    { intros n n' C Hle. exact (answers_mono env n n' a C Hle). }
    { exact H. }
    exists (S n). rewrite (intersection_target_step n cs a Hcs Ha Hs). exact (closed_fold_some _ cs Hn).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* An intersection as the assignee, to a class type or a reference: the first component that is   *)
(* taken                                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Definition searches_intersections (t: EType): Prop := match t with RootResolved _ _ _ | Generic _ => True | _ => False end.

Lemma intersection_assignee_step: forall n t cs, no_vars t = true -> forallb no_vars cs = true -> searches_intersections t ->
    is_assignable_to env (S n) (Intersection cs) t = closed_first (fun C => is_assignable_to env n C t) cs.
Proof.
    intros n t cs Ht Hcs Hs. rewrite assignable_step. destruct t as [| |[]| | | | |]; try contradiction;
        cbn [unify_step unify_root_resolved unify_generic]; exact (intersection_flipped_closed env wf n _ cs [] Ht Hcs).
Qed.

Lemma intersection_assignee_component: forall t cs, no_vars t = true -> forallb no_vars cs = true -> searches_intersections t ->
    assignable (Intersection cs) t -> exists C, In C cs /\ assignable C t.
Proof.
    intros t cs Ht Hcs Hs [n H]. destruct n as [|n]; [discriminate H|]. rewrite (intersection_assignee_step n t cs Ht Hcs Hs) in H.
    destruct (closed_first_true _ cs H) as [C [Hc HC]]. exists C. split; [exact Hc|exists n; exact HC].
Qed.

Lemma flat_target_intersection_never_fails: forall t cs C, no_vars t = true -> forallb no_vars cs = true -> searches_intersections t ->
    In C cs -> never_fails t C -> never_fails t (Intersection cs).
Proof.
    intros t cs C Ht Hcs Hs Hc H n E. destruct n as [|n]; [discriminate E|]. rewrite (intersection_assignee_step n t cs Ht Hcs Hs) in E.
    exact (closed_first_not_false _ cs C Hc (H n) E).
Qed.

Lemma intersection_assignee_answers: forall t cs, no_vars t = true -> forallb no_vars cs = true -> searches_intersections t ->
    (forall C, In C cs -> answers t C) -> answers t (Intersection cs).
Proof.
    intros t cs Ht Hcs Hs H. destruct (fuel_for_all (fun n C => is_assignable_to env n C t <> None) cs) as [n Hn].
    { intros n n' C Hle. exact (answers_mono env n n' C t Hle). }
    { exact H. }
    exists (S n). rewrite (intersection_assignee_step n t cs Ht Hcs Hs). exact (closed_first_some _ cs Hn).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A nullable target: takes a value of gfrag where what it wraps takes the value without null       *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nullable_target_step: forall n z' a, gfrag env a = true ->
    is_assignable_to env (S n) a (Nullable z') = is_assignable_to env n (without_null env a) z'.
Proof. intros n z' a Ha. unfold is_assignable_to, empty_unification. rewrite (step_nullable_any env n z' a [] Ha). reflexivity. Qed.

Lemma below_nullable: forall x z', gfrag env x = true -> assignable x (Nullable z') <-> assignable (without_null env x) z'.
Proof.
    intros x z' Hx. split; intros [n H].
    - destruct n as [|n]; [discriminate H|]. exists n. rewrite (nullable_target_step n z' x Hx) in H. exact H.
    - exists (S n). rewrite (nullable_target_step n z' x Hx). exact H.
Qed.

Lemma nullable_target_never_fails: forall z' x, gfrag env x = true -> never_fails z' (without_null env x) -> never_fails (Nullable z') x.
Proof. intros z' x Hx H n E. destruct n as [|n]; [discriminate E|]. rewrite (nullable_target_step n z' x Hx) in E. exact (H n E). Qed.

Lemma nullable_target_strip: forall z' x, gfrag env x = true -> never_fails (Nullable z') x -> never_fails z' (without_null env x).
Proof. intros z' x Hx H n E. apply (H (S n)). rewrite (nullable_target_step n z' x Hx). exact E. Qed.

Lemma nullable_target_answers: forall z' x, gfrag env x = true -> answers z' (without_null env x) -> answers (Nullable z') x.
Proof. intros z' x Hx [n H]. exists (S n). rewrite (nullable_target_step n z' x Hx). exact H. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A possibly null value is rejected by a class type, a reference, and an intersection of gfrag    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nullable_rejected: forall n t x, gfrag env t = true -> flat t -> is_assignable_to env n (Nullable x) t <> Some true.
Proof.
    intros n t x Ht Hf H. destruct n as [|n]; [discriminate H|]. destruct t as [| |[]| | | |cs|]; try contradiction.
    - discriminate H.
    - discriminate H.
    - unfold is_assignable_to, empty_unification in H. destruct (unify env (S n) (Intersection cs) (Nullable x) (Ongoing [])) as [[s'|]|] eqn:E; try discriminate H.
      exact (inter_takes_no_nullable_any env (S n) cs x [] s' Ht E).
Qed.

(* Through a nullable type, of the two sides: a class type to it, or a nullable type *)
Lemma below_nullable_root: forall m c args y, assignable (RootResolved m c args) (Nullable y) <-> assignable (RootResolved m c args) y.
Proof.
    intros m c args y. split; intros [n H]; [destruct n as [|n]; [discriminate H|]; exists n; exact H|exists (S n); exact H].
Qed.

Lemma below_nullable_nullable: forall x' y, assignable (Nullable x') (Nullable y) <-> assignable x' y.
Proof.
    intros x' y. split; intros [n H]; [destruct n as [|n]; [discriminate H|]; exists n; exact H|exists (S n); exact H].
Qed.

Lemma nullable_not_below_root: forall x' m c args, ~ assignable (Nullable x') (RootResolved m c args).
Proof. intros x' m c args [n H]. destruct n as [|n]; discriminate H. Qed.

End Rules.

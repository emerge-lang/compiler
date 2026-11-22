(*
 * Union types, `A | B`: a value of the union is a value of one of the components, as the frontend
 * builds them (BoundUnionTypeReference). First, what unify decides of them on the class fragment of
 * Transitivity.v and unions of its types, nullable or not (ufrag):
 *
 * - a union assignee is taken exactly where each of its components is (union_below_iff);
 * - a union target takes a value exactly where one of its components does (union_takes_component,
 *   below_union_of_component), also made nullable (nullable_union_takes_component): what an
 *   exhaustiveness check of `when` over the components of a union rests on;
 * - unify terminates on the fragment where it does on class types (ufrag_terminates), and is
 *   reflexive (ufrag_reflexive) and transitive (ufrag_transitive) on it.
 *
 * Unify on a union is a search: the target takes an assignee with the first component that does
 * (Subtyping.union_body), as an intersection assignee is tried component by component. So the
 * theorems that say an assignment is accepted take that unify terminates on the class types of the
 * program (terminates), as those of Generics.v do (Conjectures.unify_terminates_on, from which it
 * follows: terminates_on_classes). Ops.unify_respects_mutability covers unions already: a union is
 * assigned as the join of what its components are assigned as.
 *
 * Then the same with type parameters and intersections (UnionsInGenericCode): on the fragment of
 * Generics.v with unions at the top (Fragment.ugfrag, whose components are non-null), a union is
 * below a type exactly where each of its components is (union_below_iff_in_generic_code), a union
 * takes a class type or a reference with one of its components (union_target_component) and an
 * intersection as a whole or by a component of it (union_target_intersection), and unify never
 * rejects what transitivity says it should take (transitivity_never_fails_with_unions, from
 * Generics.transitivity_never_fails); where unify terminates on gfrag, it does on the fragment with
 * unions, components that keep their nullability included (kugfrag_terminates), and transitivity
 * is as usual (transitivity_terminating_with_unions).
 *)

From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

Section Unions.

Variable env: Environment.
Hypothesis wf: wellformed env.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* Class types, nullable or not (Transitivity.in_fragment), and non-empty unions of types of the
   fragment, nullable or not: `A | B`, `(A | B)?`, `A? | B`, `(A | B) | C` *)
Fixpoint ufrag (t: EType): bool :=
    match t with
    | Union us => negb (Nat.eqb (length us) 0) && forallb ufrag us
    | Nullable (Union us) => negb (Nat.eqb (length us) 0) && forallb ufrag us
    | _ => in_fragment env t
    end.

(* A type of the fragment is a class type, or a union, or a nullable union *)
Lemma ufrag_cases: forall t, ufrag t = true ->
    in_fragment env t = true
    \/ (exists us, t = Union us /\ us <> [] /\ forall C, In C us -> ufrag C = true)
    \/ (exists us, t = Nullable (Union us) /\ us <> [] /\ forall C, In C us -> ufrag C = true).
Proof.
    intros [m c args|[m c args|n|g|me msg|v o n|g|cs|us]|g|me msg|v o n|g|cs|us] H; try (left; exact H).
    - right. right. cbn [ufrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
    - right. left. cbn [ufrag] in H. apply andb_true_iff in H. destruct H as [Hl H]. exists us.
      split; [reflexivity|]. split; [destruct us; [discriminate Hl|discriminate]|]. apply forallb_forall, H.
Qed.

Lemma ufrag_nullable: forall y, ufrag (Nullable y) = true -> ufrag y = true.
Proof. intros [m c args|n|g|me msg|v o n|g|cs|us] H; first [exact H|discriminate H]. Qed.

Lemma ufrag_components: forall us, ufrag (Union us) = true -> forall C, In C us -> ufrag C = true.
Proof. intros us H C Hc. cbn [ufrag] in H. apply andb_true_iff in H. rewrite forallb_forall in H. exact (proj2 H C Hc). Qed.

(* The types of the fragment unify sees: class types, nullable types and unions, none of them a type
   variable or erroneous *)
Lemma ufrag_shape: forall t, ufrag t = true -> match t with RootResolved _ _ _ | Nullable _ | Union _ => True | _ => False end.
Proof.
    intros t H. destruct (ufrag_cases t H) as [Hf|[[us [-> _]]|[us [-> _]]]]; try exact I.
    destruct (fragment_cases env t Hf) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact I.
Qed.

Lemma in_fragment_no_vars: forall t, in_fragment env t = true -> no_vars t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (fragment_cases env t H) as [[m [c [args ->]]]|[m [c [args [-> H']]]]].
    - cbn [no_vars]. apply forallb_forall. intros a Ha. destruct (root_in_fragment env m c args H) as [_ Hargs].
      pose proof (Hargs a Ha) as Hf. pose proof (esize_in args a Ha) as Hs.
      destruct a as [| | | |v o n| | |]; try discriminate Hf. cbn [argument_in_fragment] in Hf. cbn [esize] in Hs.
      cbn [no_vars]. apply (IH (esize n)); [cbn [esize]; lia|reflexivity|exact Hf].
    - exact (IH (esize (RootResolved m c args)) ltac:(cbn [esize]; lia) (RootResolved m c args) eq_refl H').
Qed.

Lemma ufrag_no_vars: forall t, ufrag t = true -> no_vars t = true.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> H.
    destruct (ufrag_cases t H) as [Hf|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]]; [exact (in_fragment_no_vars t Hf)| |];
        cbn [no_vars]; apply forallb_forall; intros C Hc; pose proof (esize_in us C Hc);
        apply (IH (esize C)); [cbn [esize]; lia|reflexivity|exact (Hus C Hc)|cbn [esize]; lia|reflexivity|exact (Hus C Hc)].
Qed.

Lemma components_no_vars: forall us, ufrag (Union us) = true -> forallb no_vars us = true.
Proof. intros us H. exact (ufrag_no_vars (Union us) H). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Unify on unions, one step                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* On types without type variables, unify keeps the variable states (States.unify_free) *)
Lemma keeps_states: forall n t a s s', no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s') -> s' = s.
Proof.
    intros n t a s s' Ht Ha H. pose proof (unify_free env wf n t a s s _ Ht Ha H) as E.
    rewrite H in E. injection E as ->. reflexivity.
Qed.

(* A union target takes an assignee that is a type of values with the first component that takes it *)
Lemma unify_union_target: forall n us a s, forallb no_vars us = true ->
    match a with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    unify env (S n) (Union us) a (Ongoing s)
    = match find_first (fun C => unify env n C a (Ongoing s)) us with
      | Some (Some (_, s')) => Some (Ongoing s')
      | Some None => Some Failed
      | None => None
      end.
Proof.
    intros n us a s Hus Ha.
    change (unify env (S n) (Union us) a (Ongoing s)) with (unify_step env (unify env n) (Union us) a s).
    unfold unify_step, unify_union, union_body. destruct (no_vars_filter us Hus) as [Hv Hnv].
    destruct a as [| | | | | | |]; try contradiction; cbn zeta; rewrite Hv, Hnv, app_nil_r;
        destruct (find_first _ us) as [[[C s']|]|]; reflexivity.
Qed.

(* A union assignee is unified with the target component by component *)
Lemma unify_union_assignee: forall n t us s, match t with RootResolved _ _ _ | Nullable _ | Union _ => True | _ => False end ->
    unify env (S n) t (Union us) (Ongoing s) = fold_unify (fun inner C => unify env n t C inner) us (Ongoing s).
Proof. intros n [m c args|x|g|me msg|v o x|g|cs|ts] us s H; try contradiction; reflexivity. Qed.

Lemma fold_all: forall n t us s, (forall C, In C us -> unify env n t C (Ongoing s) = Some (Ongoing s)) ->
    fold_unify (fun inner C => unify env n t C inner) us (Ongoing s) = Some (Ongoing s).
Proof.
    intros n t us s H. induction us as [|C us IH]; [reflexivity|]. simpl. rewrite (H C (or_introl eq_refl)).
    apply IH. intros C' Hc. apply H. right. exact Hc.
Qed.

Lemma fold_answers: forall n t us s, no_vars t = true -> forallb no_vars us = true ->
    (forall C, In C us -> unify env n t C (Ongoing s) <> None) ->
    fold_unify (fun inner C => unify env n t C inner) us (Ongoing s) <> None.
Proof.
    intros n t us s Ht Hus H. induction us as [|C us IH]; [discriminate|]. simpl in Hus |- *. apply andb_true_iff in Hus.
    destruct (unify env n t C (Ongoing s)) as [[s'|]|] eqn:E.
    - rewrite (keeps_states n t C s s' Ht (proj1 Hus) E). apply IH; [exact (proj2 Hus)|]. intros C' Hc. apply H. right. exact Hc.
    - rewrite fold_unify_stays_failed_assignee. discriminate.
    - exfalso. exact (H C (or_introl eq_refl) E).
Qed.

Lemma find_first_answers: forall (f: EType -> option Unification) us, (forall C, In C us -> f C <> None) -> find_first f us <> None.
Proof.
    intros f us H. induction us as [|C us IH]; [discriminate|]. simpl.
    destruct (f C) as [[s'|]|] eqn:E; [discriminate|apply IH; intros C' Hc; apply H; right; exact Hc|exfalso; exact (H C (or_introl eq_refl) E)].
Qed.

(* Where every attempt answers and one of them succeeds, the search finds a success *)
Lemma find_first_success: forall (f: EType -> option Unification) us C s', (forall C', In C' us -> f C' <> None) ->
    In C us -> f C = Some (Ongoing s') -> exists C0 s0, find_first f us = Some (Some (C0, s0)).
Proof.
    intros f us. induction us as [|D us IH]; intros C s' Hall Hin Hc; [destruct Hin|]. simpl.
    destruct (f D) as [[s0|]|] eqn:E.
    - exists D, s0. reflexivity.
    - destruct Hin as [<-|Hin]; [rewrite Hc in E; discriminate E|].
      apply (IH C s'); [intros C' Hc'; apply Hall; right; exact Hc'|exact Hin|exact Hc].
    - exfalso. exact (Hall D (or_introl eq_refl) E).
Qed.

Lemma answers_mono: forall n n' t a s, n <= n' -> unify env n t a (Ongoing s) <> None -> unify env n' t a (Ongoing s) <> None.
Proof.
    intros n n' t a s Hle H E. destruct (unify env n t a (Ongoing s)) as [u|] eqn:E0; [|exact (H eq_refl)].
    rewrite (unify_fuel_monotone env n n' _ _ _ u Hle E0) in E. discriminate E.
Qed.

(* One fuel for all the components, where each has one of its own *)
Lemma fuel_for_all: forall (W: nat -> EType -> Prop) us, (forall n n' C, n <= n' -> W n C -> W n' C) ->
    (forall C, In C us -> exists n, W n C) -> exists n, forall C, In C us -> W n C.
Proof.
    intros W us Hmono H. induction us as [|C us IH]; [exists 0; intros C' []|].
    destruct (H C (or_introl eq_refl)) as [n0 H0]. destruct IH as [n1 H1]; [intros C' Hc; apply H; right; exact Hc|].
    exists (max n0 n1). intros C' [<-|Hc]; [apply (Hmono n0); [lia|exact H0]|apply (Hmono n1); [lia|exact (H1 C' Hc)]].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What unify decides of unions                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* x is assignable to y, with some fuel *)
Definition assignable (x y: EType): Prop := exists n, is_assignable_to env n x y = Some true.

Lemma assignable_unify: forall x y, assignable x y <-> exists n s', unify env n y x (Ongoing []) = Some (Ongoing s').
Proof.
    intros x y. unfold assignable. split.
    - intros [n H]. unfold is_assignable_to, empty_unification in H.
      destruct (unify env n y x (Ongoing [])) as [[s'|]|] eqn:E; try discriminate H. exists n, s'. exact E.
    - intros [n [s' H]]. exists n.
      exact (f_equal (option_map (fun u => match u with Ongoing _ => true | Failed => false end)) H).
Qed.

(* Of types without type variables, with the states it started with *)
Lemma assignable_free: forall x y, no_vars x = true -> no_vars y = true ->
    assignable x y <-> exists n, unify env n y x (Ongoing []) = Some (Ongoing []).
Proof.
    intros x y Hx Hy. rewrite assignable_unify. split.
    - intros [n [s' H]]. exists n. rewrite (keeps_states n y x [] s' Hy Hx H) in H. exact H.
    - intros [n H]. exists n, []. exact H.
Qed.

Lemma assignable_mono: forall n n' x y, n <= n' -> unify env n y x (Ongoing []) = Some (Ongoing []) ->
    unify env n' y x (Ongoing []) = Some (Ongoing []).
Proof. intros n n' x y Hle H. exact (unify_fuel_monotone env n n' _ _ _ _ Hle H). Qed.

(* A union assignee is taken exactly where each of its components is: `A | B` is below z iff A and B are *)
Theorem union_below_iff: forall us z, ufrag (Union us) = true -> ufrag z = true ->
    assignable (Union us) z <-> forall C, In C us -> assignable C z.
Proof.
    intros us z Hus Hz. pose proof (ufrag_shape z Hz) as Hsz. pose proof (ufrag_no_vars z Hz) as Hvz.
    pose proof (components_no_vars us Hus) as Hvus. rewrite forallb_forall in Hvus. split.
    - intros H C Hc. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
      rewrite (unify_union_assignee n z us [] Hsz) in H.
      destruct (fold_unify_each_assignee env n z us [] s' H C Hc) as [s0 [s1 Hu]].
      apply assignable_free; [exact (Hvus C Hc)|exact Hvz|]. exists n.
      pose proof (unify_free env wf n z C s0 [] _ Hvz (Hvus C Hc) Hu) as E. exact E.
    - intros H. apply assignable_free; [exact (ufrag_no_vars _ Hus)|exact Hvz|].
      destruct (fuel_for_all (fun n C => unify env n z C (Ongoing []) = Some (Ongoing [])) us) as [n Hn].
      + intros n n' C Hle Hc. exact (assignable_mono n n' C z Hle Hc).
      + intros C Hc. destruct (proj1 (assignable_free C z (Hvus C Hc) Hvz) (H C Hc)) as [n Hn]. exists n. exact Hn.
      + exists (S n). rewrite (unify_union_assignee n z us [] Hsz). exact (fold_all n z us [] Hn).
Qed.

(* A union target takes a value with one of its components: a value of `A | B` is an A or a B. That
   holds of every assignee that is a type of values, not only those of the fragment *)
Theorem union_takes_component: forall us x, ufrag (Union us) = true ->
    match x with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    assignable x (Union us) -> exists C, In C us /\ assignable x C.
Proof.
    intros us x Hus Hsx H. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
    rewrite (unify_union_target n us x [] (components_no_vars us Hus) Hsx) in H.
    destruct (find_first (fun C => unify env n C x (Ongoing [])) us) as [[[C s0]|]|] eqn:E; try discriminate H.
    destruct (find_first_found _ _ _ _ E) as [Hc Hu]. exists C. split; [exact Hc|]. apply assignable_unify. exists n, s0. exact Hu.
Qed.

(* The same through a nullable union: a value of `(A | B)?` that isn't null is an A or a B *)
Theorem nullable_union_takes_component: forall us x, ufrag (Union us) = true -> in_fragment env x = true ->
    assignable x (Nullable (Union us)) -> exists C, In C us /\ assignable x (Nullable C).
Proof.
    intros us x Hus Hx H. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
    destruct (fragment_cases env x Hx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]].
    - (* a value of a class type: the union takes it *)
      change (unify env n (Union us) (RootResolved m c args) (Ongoing []) = Some (Ongoing s')) in H.
      destruct (union_takes_component us (RootResolved m c args) Hus I) as [C [Hc HC]]; [apply assignable_unify; exists n, s'; exact H|].
      exists C. split; [exact Hc|]. apply assignable_unify in HC. destruct HC as [n0 [s0 HC]]. apply assignable_unify. exists (S n0), s0. exact HC.
    - (* a value that may be null: the union takes the value *)
      change (unify env n (Union us) (RootResolved m c args) (Ongoing []) = Some (Ongoing s')) in H.
      destruct (union_takes_component us (RootResolved m c args) Hus I) as [C [Hc HC]]; [apply assignable_unify; exists n, s'; exact H|].
      exists C. split; [exact Hc|]. apply assignable_unify in HC. destruct HC as [n0 [s0 HC]]. apply assignable_unify. exists (S n0), s0. exact HC.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Termination, reflexivity and transitivity on the fragment                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* Unify terminates on the class types of the program: as Generics.v takes it of the fragment of type
   parameters and intersections (Conjectures.unify_terminates_on), from which it follows *)
Hypothesis terminates: forall t a, in_fragment env t = true -> in_fragment env a = true ->
    exists n, unify env n t a (Ongoing []) <> None.

(* Then it terminates on the fragment of unions, too: the components are tried one by one *)
Lemma ufrag_terminates: forall t a, ufrag t = true -> ufrag a = true -> exists n, unify env n t a (Ongoing []) <> None.
Proof.
    intros t a. remember (esize t + esize a) as k eqn:Hk. revert t a Hk. induction k as [k IH] using lt_wf_ind. intros t a -> Ht Ha.
    pose proof (ufrag_no_vars t Ht) as Hvt. pose proof (ufrag_shape t Ht) as Hst.
    (* a union assignee: each component, with fuel for all of them *)
    assert (Hflip: forall us, ufrag (Union us) = true -> esize (Union us) <= esize a ->
        exists n, unify env n t (Union us) (Ongoing []) <> None).
    { intros us Hus Hsz. pose proof (ufrag_components us Hus) as Hcs.
      destruct (fuel_for_all (fun n C => unify env n t C (Ongoing []) <> None) us) as [n Hn].
      - intros n n' C Hle H. exact (answers_mono n n' t C [] Hle H).
      - intros C Hc. pose proof (esize_in us C Hc). apply (IH (esize t + esize C)); [cbn [esize] in Hsz; lia|reflexivity|exact Ht|exact (Hcs C Hc)].
      - exists (S n). rewrite (unify_union_assignee n t us [] Hst). apply fold_answers; [exact Hvt|exact (components_no_vars us Hus)|exact Hn]. }
    (* a union target, and an assignee that is a type of values: the first component that takes it *)
    assert (Hsearch: forall us, ufrag (Union us) = true -> esize (Union us) <= esize t ->
        match a with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end ->
        exists n, unify env n (Union us) a (Ongoing []) <> None).
    { intros us Hus Hsz Hsa. pose proof (ufrag_components us Hus) as Hcs.
      destruct (fuel_for_all (fun n C => unify env n C a (Ongoing []) <> None) us) as [n Hn].
      - intros n n' C Hle H. exact (answers_mono n n' C a [] Hle H).
      - intros C Hc. pose proof (esize_in us C Hc). apply (IH (esize C + esize a)); [cbn [esize] in Hsz; lia|reflexivity|exact (Hcs C Hc)|exact Ha].
      - exists (S n). rewrite (unify_union_target n us a [] (components_no_vars us Hus) Hsa).
        destruct (find_first _ us) as [[[C s']|]|] eqn:E; [discriminate|discriminate|]. exfalso. exact (find_first_answers (fun C => unify env n C a (Ongoing [])) us Hn E). }
    destruct (ufrag_cases t Ht) as [Hft|[[us [-> [Hne Hus]]]|[us [-> [Hne Hus]]]]].
    - (* a class type, nullable or not *)
      destruct (ufrag_cases a Ha) as [Hfa|[[zs [-> [Hnea Has]]]|[zs [-> [Hnea Has]]]]].
      + exact (terminates t a Hft Hfa).
      + exact (Hflip zs Ha (le_n _)).
      + destruct (fragment_cases env t Hft) as [[m [c [args ->]]]|[m [c [args [-> Hf']]]]].
        * exists 1. discriminate.
        * destruct (IH (esize (RootResolved m c args) + esize (Union zs)) ltac:(cbn [esize]; lia) (RootResolved m c args) (Union zs) eq_refl Hf' Ha) as [n Hn].
          exists (S n). exact Hn.
    - (* a union *)
      destruct (ufrag_cases a Ha) as [Hfa|[[zs [-> [Hnea Has]]]|[zs [-> [Hnea Has]]]]].
      + apply (Hsearch us Ht (le_n _)). destruct (fragment_cases env a Hfa) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact I.
      + exact (Hflip zs Ha (le_n _)).
      + exact (Hsearch us Ht (le_n _) I).
    - (* a nullable union *)
      destruct (ufrag_cases a Ha) as [Hfa|[[zs [-> [Hnea Has]]]|[zs [-> [Hnea Has]]]]].
      + destruct (fragment_cases env a Hfa) as [[m [c [args ->]]]|[m [c [args [-> Hf']]]]].
        * destruct (IH (esize (Union us) + esize (RootResolved m c args)) ltac:(cbn [esize]; lia) (Union us) (RootResolved m c args) eq_refl Ht Ha) as [n Hn].
          exists (S n). exact Hn.
        * destruct (IH (esize (Union us) + esize (RootResolved m c args)) ltac:(cbn [esize]; lia) (Union us) (RootResolved m c args) eq_refl Ht Hf') as [n Hn].
          exists (S n). exact Hn.
      + exact (Hflip zs Ha (le_n _)).
      + destruct (IH (esize (Union us) + esize (Union zs)) ltac:(cbn [esize]; lia) (Union us) (Union zs) eq_refl Ht Ha) as [n Hn].
        exists (S n). exact Hn.
Qed.

(* What is below a component is below the union *)
Lemma below_union_of_component: forall x us C, ufrag x = true -> ufrag (Union us) = true -> In C us ->
    assignable x C -> assignable x (Union us).
Proof.
    intros x. remember (esize x) as k eqn:Hk. revert x Hk. induction k as [k IH] using lt_wf_ind. intros x -> us C Hx Hus Hc HxC.
    pose proof (ufrag_no_vars x Hx) as Hvx. pose proof (ufrag_components us Hus) as Hcs. pose proof (ufrag_no_vars (Union us) Hus) as Hvus.
    pose proof (ufrag_shape C (Hcs C Hc)) as HsC.
    apply assignable_free in HxC; [|exact Hvx|exact (ufrag_no_vars C (Hcs C Hc))]. destruct HxC as [n HxC].
    (* a value of a type that is no union: the first component that takes it *)
    assert (Hsearch: match x with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end -> assignable x (Union us)).
    { intros Hsx. apply assignable_unify.
      destruct (fuel_for_all (fun n C' => unify env n C' x (Ongoing []) <> None) us) as [n0 Hn0].
      - intros n1 n2 C' Hle H. exact (answers_mono n1 n2 C' x [] Hle H).
      - intros C' Hc'. exact (ufrag_terminates C' x (Hcs C' Hc') Hx).
      - assert (HC: unify env (max n n0) C x (Ongoing []) = Some (Ongoing [])) by (apply (assignable_mono n); [lia|exact HxC]).
        assert (Hall: forall C', In C' us -> unify env (max n n0) C' x (Ongoing []) <> None)
            by (intros C' Hc'; apply (answers_mono n0); [lia|exact (Hn0 C' Hc')]).
        destruct (find_first_success (fun C' => unify env (max n n0) C' x (Ongoing [])) us C [] Hall Hc HC) as [C0 [s0 E]].
        exists (S (max n n0)), s0. rewrite (unify_union_target (max n n0) us x [] Hvus Hsx), E. reflexivity. }
    destruct (ufrag_cases x Hx) as [Hfx|[[xs [-> [Hne Hxs]]]|[xs [-> [Hne Hxs]]]]].
    - apply Hsearch. destruct (fragment_cases env x Hfx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact I.
    - (* a union: each of its components is below C, so below the union *)
      apply (union_below_iff xs (Union us) Hx Hus). intros D Hd. pose proof (esize_in xs D Hd).
      apply (IH (esize D) ltac:(cbn [esize]; lia) D eq_refl us C (Hxs D Hd) Hus Hc).
      exact (proj1 (union_below_iff xs C Hx (Hcs C Hc)) ltac:(apply assignable_free; [exact Hvx|exact (ufrag_no_vars C (Hcs C Hc))|exists n; exact HxC]) D Hd).
    - exact (Hsearch I).
Qed.

(* Every type of the fragment is assignable to itself *)
Theorem ufrag_reflexive: forall t, ufrag t = true -> assignable t t.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t -> Ht.
    destruct (ufrag_cases t Ht) as [Hf|[[us [-> [Hne Hus]]]|[us [-> [Hne Hus]]]]].
    - exists (depth t). exact (Transitivity.reflexivity env t Hf).
    - (* each component is below the union *)
      apply (union_below_iff us (Union us) Ht Ht). intros C Hc. apply (below_union_of_component C us C (Hus C Hc) Ht Hc).
      pose proof (esize_in us C Hc). apply (IH (esize C)); [cbn [esize]; lia|reflexivity|exact (Hus C Hc)].
    - destruct (IH (esize (Union us)) ltac:(cbn [esize]; lia) (Union us) eq_refl Ht) as [n H]. exists (S n). exact H.
Qed.

(* An intersection with a component below a union is below the union, as every value of the
   intersection is a value of the component: `(A | B) & C` is below `A | B`. The components before
   that one have to answer *)
Theorem below_union_of_intersection_component: forall cs x us, In x cs -> assignable x (Union us) ->
    (forall y, In y cs -> exists n, unify env n (Union us) y (Ongoing []) <> None) ->
    assignable (Intersection cs) (Union us).
Proof.
    intros cs x us Hx H Hall. apply assignable_unify in H. destruct H as [n [s' H]].
    destruct (fuel_for_all (fun n y => unify env n (Union us) y (Ongoing []) <> None) cs) as [n0 Hn0].
    { intros n1 n2 y Hle Hy. exact (answers_mono n1 n2 (Union us) y [] Hle Hy). }
    { exact Hall. }
    assert (Hx': unify env (max n n0) (Union us) x (Ongoing []) = Some (Ongoing s'))
        by (apply (unify_fuel_monotone env n (max n n0) _ _ _ _); [lia|exact H]).
    assert (Hall': forall y, In y cs -> unify env (max n n0) (Union us) y (Ongoing []) <> None)
        by (intros y Hy; apply (answers_mono n0 (max n n0)); [lia|exact (Hn0 y Hy)]).
    destruct (find_first_success (fun y => unify env (max n n0) (Union us) y (Ongoing [])) cs x s' Hall' Hx Hx') as [y0 [s0 E]].
    apply assignable_unify. exists (S (max n n0)), s0.
    change (unify env (S (max n n0)) (Union us) (Intersection cs) (Ongoing []))
        with (unify_step env (unify env (max n n0)) (Union us) (Intersection cs) []).
    unfold unify_step, unify_union, intersection_flipped_unify. rewrite E. reflexivity.
Qed.

(* So `(A | B) & C` is below `A | B` on the fragment: the union is one of the components *)
Theorem intersection_with_union_below_union: forall cs us, ufrag (Union us) = true -> (forall y, In y cs -> ufrag y = true) ->
    In (Union us) cs -> assignable (Intersection cs) (Union us).
Proof.
    intros cs us Hus Hcs Hin. apply (below_union_of_intersection_component cs (Union us) us Hin (ufrag_reflexive (Union us) Hus)).
    intros y Hy. exact (ufrag_terminates (Union us) y Hus (Hcs y Hy)).
Qed.

(* Through a nullable type: a value of a class type, or one that may be null *)
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

(* Transitivity: a type below another, which is below a third, is below the third. The unions are
   taken apart into their components, down to the class types, where Transitivity.transitivity holds *)
Theorem ufrag_transitive: forall x y z, ufrag x = true -> ufrag y = true -> ufrag z = true ->
    assignable x y -> assignable y z -> assignable x z.
Proof.
    intros x y z. remember (esize x + esize y + esize z) as k eqn:Hk. revert x y z Hk. induction k as [k IH] using lt_wf_ind.
    intros x y z -> Hx Hy Hz Hxy Hyz.
    (* x a union: each of its components *)
    destruct (ufrag_cases x Hx) as [Hfx|[[xs [Ex [Hne Hxs]]]|[xs [Ex [Hne Hxs]]]]].
    2:{ subst x. apply (union_below_iff xs z Hx Hz). intros C Hc. pose proof (esize_in xs C Hc).
        apply (IH (esize C + esize y + esize z) ltac:(cbn [esize]; lia) C y z eq_refl (Hxs C Hc) Hy Hz); [|exact Hyz].
        exact (proj1 (union_below_iff xs y Hx Hy) Hxy C Hc). }
    all: assert (Hsx: match x with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end)
        by (first [destruct (fragment_cases env x Hfx) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; exact I|rewrite Ex; exact I]).
    (* y a union: one of its components takes x *)
    all: destruct (ufrag_cases y Hy) as [Hfy|[[ys [Ey [Hney Hys]]]|[ys [Ey [Hney Hys]]]]].
    all: try (subst y; destruct (union_takes_component ys x Hy Hsx Hxy) as [C [Hc HxC]]; pose proof (esize_in ys C Hc);
              apply (IH (esize x + esize C + esize z) ltac:(cbn [esize]; lia) x C z eq_refl Hx (Hys C Hc) Hz HxC);
              exact (proj1 (union_below_iff ys z Hy Hz) Hyz C Hc)).
    all: assert (Hsy: match y with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end)
        by (first [destruct (fragment_cases env y Hfy) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; exact I|rewrite Ey; exact I]).
    (* z a union: one of its components takes y, and so x *)
    all: destruct (ufrag_cases z Hz) as [Hfz|[[zs [Ez [Hnez Hzs]]]|[zs [Ez [Hnez Hzs]]]]].
    all: try (subst z; destruct (union_takes_component zs y Hz Hsy Hyz) as [C [Hc HyC]]; pose proof (esize_in zs C Hc);
              apply (below_union_of_component x zs C Hx Hz Hc);
              exact (IH (esize x + esize y + esize C) ltac:(cbn [esize]; lia) x y C eq_refl Hx Hy (Hzs C Hc) Hxy HyC)).
    (* class types, nullable or not, and nullable unions: through the nullable ones *)
    all: subst.
    all: repeat match goal with H: in_fragment env ?t = true |- _ =>
        destruct (fragment_cases env t H) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; clear H end.
    all: repeat match goal with
         | H: assignable (Nullable _) (RootResolved _ _ _) |- _ => exfalso; exact (nullable_not_below_root _ _ _ _ H)
         | H: assignable (RootResolved ?m ?c ?a) (Nullable ?y) |- _ => apply (below_nullable_root m c a y) in H
         | H: assignable (Nullable ?x') (Nullable ?y) |- _ => apply (below_nullable_nullable x' y) in H
         | |- assignable (RootResolved ?m ?c ?a) (Nullable ?y) => apply (below_nullable_root m c a y)
         | |- assignable (Nullable ?x') (Nullable ?y) => apply (below_nullable_nullable x' y)
         end.
    all: first
        [ destruct Hxy as [n1 H1]; destruct Hyz as [n2 H2]; exists (n1 + n2); exact (Transitivity.transitivity env wf n1 n2 _ _ _ Hx Hy Hz H1 H2)
        | refine (IH _ _ _ _ _ eq_refl _ _ _ Hxy Hyz); [cbn [esize]; lia|..];
          first [exact Hx|exact Hy|exact Hz|apply ufrag_nullable; first [exact Hx|exact Hy|exact Hz]] ].
Qed.

End Unions.

Section UnionsInGenericCode.

Variable env: Environment.
Hypothesis wf: wellformed env.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

Let never_fails := Generics.never_fails env.
Let assignable := Unions.assignable env.

(* ---------------------------------------------------------------------------------------------- *)
(* The fragment                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma ugfrag_no_vars: forall t, ugfrag env t = true -> no_vars t = true.
Proof.
    intros t H. destruct (ugfrag_cases env t H) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]]; [exact (gfrag_no_vars env t Hg)| |];
        cbn [no_vars]; apply forallb_forall; intros C Hc; exact (gfrag_no_vars env C (union_component_gfrag env C (Hus C Hc))).
Qed.

Lemma union_components_no_vars: forall us, ugfrag env (Union us) = true -> forallb no_vars us = true.
Proof. intros us H. exact (ugfrag_no_vars (Union us) H). Qed.

Lemma component_gfrag: forall us C, ugfrag env (Union us) = true -> In C us -> gfrag env C = true.
Proof. intros us C H Hc. exact (union_component_gfrag env C (proj2 (ugfrag_union env us H) C Hc)). Qed.

Lemma component_flat: forall us C, ugfrag env (Union us) = true -> In C us -> flat C.
Proof. intros us C H Hc. exact (union_component_flat env C (proj2 (ugfrag_union env us H) C Hc)). Qed.

Lemma component_nullable_gfrag: forall us C, ugfrag env (Union us) = true -> In C us -> gfrag env (Nullable C) = true.
Proof. intros us C H Hc. exact (union_component_nullable_gfrag env C (proj2 (ugfrag_union env us H) C Hc)). Qed.

(* A component of an intersection of the fragment: a class type, a reference, or one of them made nullable *)
Lemma intersection_component_shape: forall cs C, gfrag env (Intersection cs) = true -> In C cs ->
    match C with RootResolved _ _ _ | Generic _ | Nullable _ => True | _ => False end.
Proof.
    intros cs C H Hc. destruct (intersection_gfrag_cases env cs H) as [_ [_ [Hk|[Hk _]]]]; specialize (Hk C Hc);
        destruct C as [| | | | | | |]; cbn [is_component is_kept_component] in Hk; first [exact I|discriminate Hk].
Qed.

Lemma intersection_component_gfrag: forall cs C, gfrag env (Intersection cs) = true -> In C cs -> gfrag env C = true.
Proof. intros cs C H Hc. exact (proj2 (intersection_components env cs H) C Hc). Qed.

(* A component of a non-null intersection, made nullable, is of the fragment *)
Lemma nullable_component_gfrag: forall zs C, gfrag env (Nullable (Intersection zs)) = true -> In C zs -> gfrag env (Nullable C) = true.
Proof.
    intros zs C H Hc. change (non_null env (Intersection zs) && gfrag env (Intersection zs) = true) in H.
    apply andb_true_iff in H. destruct H as [Hnn Hzs]. cbn [non_null] in Hnn.
    destruct (intersection_gfrag env zs Hzs (proj1 (negb_true_iff _) Hnn)) as [_ Hcs]. destruct (Hcs C Hc) as [Hcomp HC].
    change (non_null env C && gfrag env C = true). rewrite HC, andb_true_r.
    destruct C as [| | | | | | |]; cbn [is_component] in Hcomp; try discriminate Hcomp; exact Hcomp.
Qed.

Lemma nullable_intersection_gfrag: forall zs, gfrag env (Nullable (Intersection zs)) = true -> gfrag env (Intersection zs) = true.
Proof.
    intros zs H. change (non_null env (Intersection zs) && gfrag env (Intersection zs) = true) in H. apply andb_true_iff in H. exact (proj2 H).
Qed.

(* Without null, an intersection of the fragment is the intersection of its components without null: as they are,
   where they are non-null *)
Lemma without_null_intersection: forall cs, gfrag env (Intersection cs) = true ->
    without_null env (Intersection cs) = Intersection (map (without_null env) cs).
Proof.
    intros cs H. cbn [without_null]. destruct (forallb (is_nullable env) cs) eqn:E; [reflexivity|].
    f_equal. symmetry. transitivity (map id cs); [|apply map_id]. apply map_ext_in. intros C Hc. apply without_null_unchanged.
    destruct (intersection_gfrag env cs H) as [_ Hcs]; [exact E|]. exact (is_component_not_nullable env C (proj1 (Hcs C Hc))).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Unify on unions, one step                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* A union assignee is unified with the target component by component *)
Lemma step_union_assignee: forall n t us s, match t with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end ->
    unify env (S n) t (Union us) (Ongoing s) = fold_unify (fun inner C => unify env n t C inner) us (Ongoing s).
Proof. intros n [m c args|x|[gm nn p vs]|me msg|v o x|g|cs|ts] us s H; try contradiction; reflexivity. Qed.

(* A union target takes a value of a type of values with the first component that does *)
Lemma step_union_target: forall n us a s, match a with RootResolved _ _ _ | Nullable _ | Generic _ => True | _ => False end ->
    unify env (S n) (Union us) a (Ongoing s) = union_body (unify env n) us a s.
Proof. intros n us [m c args|x|[gm nn p vs]|me msg|v o x|g|cs|ts] s H; try contradiction; reflexivity. Qed.

(* ... and an intersection with a component of it that is below the whole union, or else with a component of
   its own that takes the intersection *)
Lemma step_union_intersection: forall n us cs s,
    unify env (S n) (Union us) (Intersection cs) (Ongoing s)
    = match intersection_flipped_unify (unify env n) (Union us) cs s with
      | Some Failed => union_body (unify env n) us (Intersection cs) s
      | r => r
      end.
Proof. reflexivity. Qed.

(* On types without type variables, a success in some states is one in every *)
Lemma free_success: forall n t a s s' s0, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing s) = Some (Ongoing s') -> unify env n t a (Ongoing s0) = Some (Ongoing s0).
Proof. intros n t a s s' s0 Ht Ha H. exact (unify_free env wf n t a s s0 _ Ht Ha H). Qed.

Lemma takes_assignable: forall n x y s, no_vars x = true -> no_vars y = true ->
    unify env n y x (Ongoing s) = Some (Ongoing s) -> assignable x y.
Proof. intros n x y s Hx Hy H. apply assignable_unify. exists n, []. exact (free_success n y x s s [] Hy Hx H). Qed.

Lemma assignable_takes: forall x y, no_vars x = true -> no_vars y = true ->
    assignable x y -> exists n, forall s, unify env n y x (Ongoing s) = Some (Ongoing s).
Proof.
    intros x y Hx Hy H. apply (assignable_free env wf x y Hx Hy) in H. destruct H as [n H]. exists n. intros s.
    exact (free_success n y x [] [] s Hy Hx H).
Qed.

(* unify never rejecting, from the answers it gives from empty states *)
Lemma never_fails_of_answers: forall z x, no_vars z = true -> no_vars x = true ->
    (forall n, is_assignable_to env n x z <> Some false) -> never_fails z x.
Proof.
    intros z x Hz Hx H n s E. apply (H n). unfold is_assignable_to, empty_unification.
    rewrite (unify_free env wf n z x s [] _ Hz Hx E). reflexivity.
Qed.

Lemma find_first_all_failed: forall (f: EType -> option Unification) xs, find_first f xs = Some None ->
    forall x, In x xs -> f x = Some Failed.
Proof.
    intros f xs. induction xs as [|y xs IH]; intros H x Hx; [destruct Hx|]. simpl in H.
    destruct (f y) as [[s|]|] eqn:E; try discriminate H. destruct Hx as [<-|Hx]; [exact E|exact (IH H x Hx)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the assignee: taken where each component is                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* A target that is no intersection took the union component by component *)
Lemma union_assignee_flat_target: forall n t us s, match t with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end ->
    no_vars t = true -> forallb no_vars us = true ->
    unify env (S n) t (Union us) (Ongoing s) = Some (Ongoing s) -> forall C, In C us -> unify env n t C (Ongoing s) = Some (Ongoing s).
Proof.
    intros n t us s Hshape Ht Hus H C Hc. rewrite (step_union_assignee n t us s Hshape) in H.
    destruct (fold_unify_each_assignee env n t us s s H C Hc) as [s0 [s1 Hu]]. rewrite forallb_forall in Hus.
    exact (free_success n t C s0 s1 s Ht (Hus C Hc) Hu).
Qed.

Theorem union_assignee_components: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    assignable (Union us) y -> forall C, In C us -> assignable C y.
Proof.
    intros us y Hus Hy H C Hc. pose proof (union_components_no_vars us Hus) as Hvus. pose proof (ugfrag_no_vars y Hy) as Hvy.
    pose proof (gfrag_no_vars env C (component_gfrag us C Hus Hc)) as Hvc.
    destruct (assignable_takes (Union us) y Hvus Hvy H) as [n Hn]. destruct n as [|n]; [discriminate (Hn [])|].
    pose proof (ugfrag_shape env y Hy) as Hsy.
    assert (Hflat: match y with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end -> assignable C y).
    { intros Hs. exact (takes_assignable n C y [] Hvc Hvy (union_assignee_flat_target n y us [] Hs Hvy Hvus (Hn []) C Hc)). }
    destruct y as [m c args|yn|g|me msg|v o yn|g|ys|ys]; try contradiction; try (apply Hflat; exact I).
    (* an intersection: each of its components took the union, so takes the component, so the intersection does *)
    pose proof (inter_target_all env wf n ys (Union us) [] [] (gfrag_components_no_vars env ys Hy) Hvus I (Hn []))as Hall.
    destruct n as [|n]; [destruct (intersection_components env ys Hy) as [Hne _]; destruct ys as [|Y ys]; [contradiction (Hne eq_refl)|discriminate (Hall Y (or_introl eq_refl))]|].
    apply (takes_assignable (S (S n)) C (Intersection ys) [] Hvc Hvy).
    apply inter_target_takes; [exact (gfrag_components_no_vars env ys Hy)|exact (proj1 (intersection_components env ys Hy))| |].
    - pose proof (component_flat us C Hus Hc) as Hfc. destruct C as [| | | | | | |]; try contradiction; exact I.
    - intros Y Hin. pose proof (intersection_component_shape ys Y Hy Hin) as Hsh.
      pose proof (gfrag_no_vars env Y (intersection_component_gfrag ys Y Hy Hin)) as Hvy'.
      apply (unify_fuel_monotone env n (S n) Y C _ _ (le_S _ _ (le_n _))).
      exact (union_assignee_flat_target n Y us [] ltac:(destruct Y as [| | | | | | |]; try contradiction; exact I) Hvy' Hvus (Hall Y Hin) C Hc).
Qed.

(* The converse: a union is taken where each of its components is *)
Theorem union_assignee_taken: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    (forall C, In C us -> assignable C y) -> assignable (Union us) y.
Proof.
    intros us y Hus Hy H. pose proof (union_components_no_vars us Hus) as Hvus. pose proof (ugfrag_no_vars y Hy) as Hvy.
    destruct (ugfrag_union env us Hus) as [Hne Hcs].
    destruct (fuel_for_all (fun n C => unify env n y C (Ongoing []) = Some (Ongoing [])) us) as [n Hn].
    { intros n n' C Hle Hc. exact (assignable_mono env n n' C y Hle Hc). }
    { intros C Hc. exact (proj1 (assignable_free env wf C y (gfrag_no_vars env C (component_gfrag us C Hus Hc)) Hvy) (H C Hc)). }
    pose proof (ugfrag_shape env y Hy) as Hsy.
    assert (Hflat: match y with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end -> assignable (Union us) y).
    { intros Hs. apply (takes_assignable (S n) (Union us) y [] Hvus Hvy). rewrite (step_union_assignee n y us [] Hs). exact (fold_all env n y us [] Hn). }
    destruct y as [m c args|yn|g|me msg|v o yn|g|ys|ys]; try contradiction; try (apply Hflat; exact I).
    (* an intersection: each of its components takes each component of the union, so the union *)
    destruct n as [|n]; [destruct us as [|C us']; [contradiction (Hne eq_refl)|discriminate (Hn C (or_introl eq_refl))]|].
    pose proof (gfrag_components_no_vars env ys Hy) as Hvys.
    apply (takes_assignable (S (S n)) (Union us) (Intersection ys) [] Hvus Hvy).
    apply inter_target_takes; [exact Hvys|exact (proj1 (intersection_components env ys Hy))|exact I|].
    intros Y Hin. pose proof (intersection_component_shape ys Y Hy Hin) as Hsh.
    rewrite (step_union_assignee n Y us []); [|destruct Y as [| | | | | | |]; try contradiction; exact I].
    apply fold_all. intros C Hc. pose proof (Hn C Hc) as Hu.
    pose proof (component_flat us C Hus Hc) as Hfc.
    exact (inter_target_all env wf n ys C [] [] Hvys (gfrag_no_vars env C (component_gfrag us C Hus Hc))
        ltac:(destruct C as [| | | | | | |]; try contradiction; exact I) Hu Y Hin).
Qed.

(* A union is below a type exactly where each of its components is *)
Theorem union_below_iff_in_generic_code: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    assignable (Union us) y <-> forall C, In C us -> assignable C y.
Proof.
    intros us y Hus Hy. split; [exact (union_assignee_components us y Hus Hy)|exact (union_assignee_taken us y Hus Hy)].
Qed.

(* Where every component never fails, the union never fails, into a target that is no intersection *)
Lemma union_assignee_never_fails: forall z us, match z with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end ->
    no_vars z = true -> forallb no_vars us = true ->
    (forall C, In C us -> never_fails z C) -> never_fails z (Union us).
Proof.
    intros z us Hshape Hz Hus H. apply never_fails_step. intros n s E. rewrite (step_union_assignee n z us s Hshape) in E.
    rewrite forallb_forall in Hus.
    assert (Hfold: fold_unify (fun inner C => unify env n z C inner) us (Ongoing s) = None
        \/ fold_unify (fun inner C => unify env n z C inner) us (Ongoing s) = Some (Ongoing s)).
    { apply (fold_never_fails (fun C inner => unify env n z C inner)). intros C Hc.
      apply free_result; [exact wf|exact Hz|exact (Hus C Hc)|exact (H C Hc n s)]. }
    destruct Hfold as [Hfold|Hfold]; rewrite Hfold in E; discriminate E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the target: takes a value with one of its components                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* No component of a union takes a possibly null value: a class type, a reference and an intersection of the
   fragment reject it (a reference to a type parameter of a nullable bound, as it is, rejects `X?` too) *)
Lemma component_takes_no_nullable: forall n C x s s', is_union_component env C = true ->
    unify env n C (Nullable x) (Ongoing s) = Some (Ongoing s') -> False.
Proof.
    intros n C x s s' HC H. destruct n as [|n]; [discriminate H|]. pose proof (union_component_flat env C HC) as Hf.
    destruct C as [m c args|y|g|me msg|v o y|g|cs|us]; try contradiction.
    - change (Some Failed = Some (Ongoing s')) in H. discriminate H.
    - rewrite step_generic_nullable in H. discriminate H.
    - exact (inter_takes_no_nullable_any env (S n) cs x s s' (union_component_gfrag env _ HC) H).
Qed.

(* Only a nullable type takes a possibly null value, and takes what it wraps *)
Theorem nullable_assignee_target: forall x y, ugfrag env y = true -> assignable (Nullable x) y ->
    exists y', y = Nullable y' /\ assignable x y'.
Proof.
    intros x y Hy H. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
    destruct (ugfrag_cases env y Hy) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - destruct (gfrag_cases env y Hg) as [[m [c [args ->]]]|[[y' [-> _]]|[[gm [nn [p [vs [-> _]]]]]|[cs ->]]]].
      + exfalso. change (Some Failed = Some (Ongoing s')) in H. discriminate H.
      + exists y'. split; [reflexivity|]. rewrite unify_nullable_nullable in H. apply assignable_unify. exists n, s'. exact H.
      + exfalso. rewrite step_generic_nullable in H. discriminate H.
      + exfalso. exact (inter_takes_no_nullable_any env (S n) cs x [] s' Hg H).
    - exfalso. rewrite (step_union_target n us (Nullable x) [] I) in H.
      destruct (union_body_found env n us (Nullable x) [] s' H) as [C [Hc HC]].
      exact (component_takes_no_nullable n C x [] s' (Hus C Hc) HC).
    - exists (Union us). split; [reflexivity|]. rewrite unify_nullable_nullable in H. apply assignable_unify. exists n, s'. exact H.
Qed.

(* A value of a class type or a reference is taken by one of the components *)
Theorem union_target_component: forall us x, match x with RootResolved _ _ _ | Generic _ => True | _ => False end ->
    assignable x (Union us) -> exists C, In C us /\ assignable x C.
Proof.
    intros us x Hx H. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
    rewrite (step_union_target n us x [] ltac:(destruct x as [| | | | | | |]; try contradiction; exact I)) in H.
    destruct (union_body_found env n us x [] s' H) as [C [Hc HC]]. exists C. split; [exact Hc|].
    apply assignable_unify. exists n, s'. exact HC.
Qed.

(* An intersection is below a union by one of its components, or as a whole by a component of the union *)
Theorem intersection_assignee_below_union: forall ys zs, assignable (Intersection ys) (Union zs) ->
    (exists C, In C ys /\ assignable C (Union zs)) \/ (exists y, In y zs /\ assignable (Intersection ys) y).
Proof.
    intros ys zs H. apply assignable_unify in H. destruct H as [n [s' H]]. destruct n as [|n]; [discriminate H|].
    rewrite step_union_intersection in H.
    destruct (intersection_flipped_unify (unify env n) (Union zs) ys []) as [[s0|]|] eqn:E; try discriminate H.
    - left. destruct (intersection_flipped_unify_found env n (Union zs) ys [] s0 E) as [C [Hc HC]]. exists C. split; [exact Hc|].
      apply assignable_unify. exists n, s0. exact HC.
    - right. destruct (union_body_found env n zs (Intersection ys) [] s' H) as [y [Hy Hu]]. exists y. split; [exact Hy|].
      apply assignable_unify. exists n, s'. exact Hu.
Qed.

(* ... where the component is below one of the components of the union: `(A | B) & C` is below `A | B` by its
   component `A | B` (the frontend distributes, so the component there is `A & C`, below `A`) *)
Theorem union_target_intersection: forall us cs, ugfrag env (Union us) = true -> gfrag env (Intersection cs) = true ->
    assignable (Intersection cs) (Union us) ->
    (exists y, In y us /\ assignable (Intersection cs) y) \/ (exists C y, In C cs /\ In y us /\ assignable C y).
Proof.
    intros us cs Hus Hcs H. destruct (intersection_assignee_below_union cs us H) as [[C [Hc HCu]]|Hwhole]; [right|left; exact Hwhole].
    pose proof (intersection_component_shape cs C Hcs Hc) as Hsh.
    destruct C as [m c args|x|g|me msg|v o x|g|cs'|us']; try contradiction.
    - destruct (union_target_component us (RootResolved m c args) I HCu) as [y [Hy Hxy]]. exists (RootResolved m c args), y. auto.
    - exfalso. destruct (nullable_assignee_target x (Union us) Hus HCu) as [yn [Eq _]]. discriminate Eq.
    - destruct (union_target_component us (Generic g) I HCu) as [y [Hy Hxy]]. exists (Generic g), y. auto.
Qed.

(* A union never rejects what one of its components never rejects *)
Lemma union_target_never_fails: forall us x C, forallb no_vars us = true -> In C us -> flat x ->
    never_fails C x -> never_fails (Union us) x.
Proof.
    intros us x C Hus Hc Hx H. apply never_fails_step. intros n s E.
    assert (Hbody: union_body (unify env n) us x s <> Some Failed).
    { unfold union_body. destruct (no_vars_filter us Hus) as [Hvar Hnonvar]. cbn zeta. rewrite Hvar, Hnonvar, app_nil_r.
      destruct (find_first (fun C' => unify env n C' x (Ongoing s)) us) as [[[C0 s0]|]|] eqn:F; try discriminate.
      exfalso. exact (H n s (find_first_all_failed _ us F C Hc)). }
    destruct x as [m c args|y|g|me msg|v o y|g|cs|us']; try contradiction.
    all: try (rewrite step_union_intersection in E;
              destruct (intersection_flipped_unify (unify env n) (Union us) cs s) as [[s0|]|]; [discriminate E|exact (Hbody E)|discriminate E]).
    all: exact (Hbody E).
Qed.

(* ... nor an intersection with a component it never rejects *)
Lemma union_target_intersection_never_fails: forall us cs C, In C cs ->
    never_fails (Union us) C -> never_fails (Union us) (Intersection cs).
Proof.
    intros us cs C Hc H. apply never_fails_step. intros n s E. rewrite step_union_intersection in E.
    destruct (intersection_flipped_unify (unify env n) (Union us) cs s) as [[s0|]|] eqn:F; try discriminate E.
    exact (flipped_never_fails env n (Union us) cs s C Hc (H n s) F).
Qed.

(* Neither does a class type or a reference *)
Lemma flat_target_intersection_never_fails: forall z cs C, match z with RootResolved _ _ _ | Generic _ => True | _ => False end ->
    In C cs -> never_fails z C -> never_fails z (Intersection cs).
Proof.
    intros z cs C Hz Hc H. apply never_fails_step. intros n s E.
    destruct z as [m c args|y|g|me msg|v o y|g|zs|us]; try contradiction.
    - rewrite step_root_inter in E. exact (flipped_never_fails env n _ cs s C Hc (H n s) E).
    - rewrite step_generic_inter in E. exact (flipped_never_fails env n _ cs s C Hc (H n s) E).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Through a nullable target                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* A nullable target takes a type of gfrag where what it wraps takes the type without null (Generics.step_nullable_any) *)
Lemma nullable_target_never_fails: forall z' x, gfrag env x = true ->
    never_fails z' (without_null env x) -> never_fails (Nullable z') x.
Proof. intros z' x Hx H. apply never_fails_step. intros n s E. rewrite (step_nullable_any env n z' x s Hx) in E. exact (H n s E). Qed.

Lemma nullable_target_strip: forall z' x, gfrag env x = true ->
    never_fails (Nullable z') x -> never_fails z' (without_null env x).
Proof. intros z' x Hx H n s E. apply (H (S n) s). rewrite (step_nullable_any env n z' x s Hx). exact E. Qed.

Lemma below_nullable: forall x z', gfrag env x = true -> assignable x (Nullable z') <-> assignable (without_null env x) z'.
Proof.
    intros x z' Hx. split.
    - intros [n H]. destruct n as [|n]; [discriminate H|]. exists n. unfold is_assignable_to, empty_unification in *.
      rewrite (step_nullable_any env n z' x [] Hx) in H. exact H.
    - intros [n H]. exists (S n). unfold is_assignable_to, empty_unification in *. rewrite (step_nullable_any env n z' x [] Hx). exact H.
Qed.

(* An intersection that takes a possibly null value keeps the nullability of its components *)
Lemma nullable_below_intersection: forall y' zs, assignable (Nullable y') (Intersection zs) -> is_nullable env (Intersection zs) = true.
Proof.
    intros y' zs [n H]. destruct n as [|n]; [discriminate H|]. destruct (is_nullable env (Intersection zs)) eqn:E; [reflexivity|].
    unfold is_assignable_to, empty_unification in H. rewrite (step_inter_nullable env n zs y' [] E) in H. discriminate H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* An intersection as the target: every component takes the assignee                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma intersection_target_components: forall zs y, gfrag env (Intersection zs) = true -> ugfrag env y = true ->
    assignable y (Intersection zs) -> forall C, In C zs -> assignable y C.
Proof.
    intros zs y Hzs Hy H C Hc. pose proof (ugfrag_no_vars y Hy) as Hvy. pose proof (gfrag_components_no_vars env zs Hzs) as Hvzs.
    destruct (assignable_takes y (Intersection zs) Hvy Hvzs H) as [n Hn]. destruct n as [|n]; [discriminate (Hn [])|].
    assert (Hshape: inter_shape env zs y).
    { pose proof (ugfrag_shape env y Hy) as Hs. destruct y as [|yn| | | | | |]; try contradiction; try exact I.
      cbn [inter_shape]. destruct (is_nullable env (Intersection zs)) eqn:E; [reflexivity|].
      pose proof (Hn []) as Hu. rewrite (step_inter_nullable env n zs yn [] E) in Hu. discriminate Hu. }
    exact (takes_assignable n y C [] Hvy (gfrag_no_vars env C (intersection_component_gfrag zs C Hzs Hc))
        (inter_target_all env wf n zs y [] [] Hvzs Hvy Hshape (Hn []) C Hc)).
Qed.

Lemma nullable_intersection_target_components: forall zs y, gfrag env (Nullable (Intersection zs)) = true -> ugfrag env y = true ->
    assignable y (Nullable (Intersection zs)) -> forall C, In C zs -> assignable y (Nullable C).
Proof.
    intros zs y Hz Hy H C Hc. pose proof (nullable_intersection_gfrag zs Hz) as Hzs. pose proof (nullable_component_gfrag zs C Hz Hc) as HC.
    destruct (ugfrag_cases env y Hy) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - apply (below_nullable y C Hg).
      exact (intersection_target_components zs _ Hzs (gfrag_ugfrag env _ (gfrag_without_null env wf declared declared_wf y Hg))
          (proj1 (below_nullable y (Intersection zs) Hg) H) C Hc).
    - apply (union_assignee_taken us (Nullable C) Hy (gfrag_ugfrag env _ HC)). intros D Hd.
      pose proof (component_gfrag us D Hy Hd) as HD. apply (below_nullable D C HD).
      apply (intersection_target_components zs _ Hzs (gfrag_ugfrag env _ (gfrag_without_null env wf declared declared_wf D HD))); [|exact Hc].
      apply (below_nullable D (Intersection zs) HD). exact (union_assignee_components us _ Hy (gfrag_ugfrag env _ Hz) H D Hd).
    - apply (below_nullable_nullable env). apply (intersection_target_components zs (Union us) Hzs Hy); [|exact Hc].
      apply (below_nullable_nullable env). exact H.
Qed.

Lemma intersection_target_never_fails: forall zs x, gfrag env (Intersection zs) = true -> no_vars x = true -> inter_shape env zs x ->
    (forall C, In C zs -> never_fails C x) -> never_fails (Intersection zs) x.
Proof. intros zs x Hzs Hx Hs H. exact (inter_target_never_fails env wf zs x (gfrag_components_no_vars env zs Hzs) Hx Hs H). Qed.

Lemma nullable_intersection_target_never_fails: forall zs x, gfrag env (Intersection zs) = true -> gfrag env x = true ->
    (forall C, In C zs -> never_fails (Nullable C) x) -> never_fails (Nullable (Intersection zs)) x.
Proof.
    intros zs x Hzs Hx H. apply (nullable_target_never_fails _ x Hx).
    pose proof (gfrag_without_null env wf declared declared_wf x Hx) as Hw. pose proof (without_null_shape env x) as Hs.
    apply (intersection_target_never_fails zs _ Hzs (gfrag_no_vars env _ Hw)).
    - remember (without_null env x) as w eqn:Ew. destruct w as [| | | | | | |]; try exact I; try contradiction; simpl in Hw; discriminate Hw.
    - intros C Hc. exact (nullable_target_strip C x Hx (H C Hc)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* An intersection as the assignee                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* A target that is no intersection never rejects an intersection with a component it never rejects *)
Lemma intersection_assignee_never_fails: forall z cs C, ugfrag env z = true ->
    match z with Intersection _ | Nullable (Intersection _) => False | _ => True end ->
    gfrag env (Intersection cs) = true -> In C cs -> never_fails z C -> never_fails z (Intersection cs).
Proof.
    intros z cs C Hz Hsz Hcs Hc H. pose proof (intersection_component_gfrag cs C Hcs Hc) as HC.
    destruct (ugfrag_cases env z Hz) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - destruct (gfrag_cases env z Hg) as [[m [c [args ->]]]|[[zn [-> [Hnz Hgz]]]|[[gm [nn [p [vs [-> _]]]]]|[zs ->]]]]; try (exfalso; exact Hsz).
      + exact (flat_target_intersection_never_fails (RootResolved m c args) cs C I Hc H).
      + (* a nullable type: what it wraps never rejects the component without null, so the intersection without null *)
        apply (nullable_target_never_fails zn _ Hcs). rewrite (without_null_intersection cs Hcs).
        pose proof (nullable_target_strip zn C HC H) as H'.
        assert (Hin: In (without_null env C) (map (without_null env) cs)) by (apply in_map, Hc).
        destruct (gfrag_cases env zn Hgz) as [[m [c [args ->]]]|[[zn' [-> [Hnz' _]]]|[[gm [nn [p [vs [-> _]]]]]|[zs ->]]]].
        * exact (flat_target_intersection_never_fails (RootResolved m c args) _ _ I Hin H').
        * exfalso. cbn [non_null is_component] in Hnz. discriminate Hnz.
        * exact (flat_target_intersection_never_fails (Generic (mkGenericRef gm nn p vs)) _ _ I Hin H').
        * exfalso. exact Hsz.
      + exact (flat_target_intersection_never_fails (Generic (mkGenericRef gm nn p vs)) cs C I Hc H).
    - exact (union_target_intersection_never_fails us cs C Hc H).
    - apply (nullable_target_never_fails _ _ Hcs). rewrite (without_null_intersection cs Hcs).
      exact (union_target_intersection_never_fails us _ _ (in_map _ cs C Hc) (nullable_target_strip _ C HC H)).
Qed.

(* An intersection is below a class type or a reference, nullable or not, by one of its components *)
Lemma intersection_assignee_below_flat: forall ys z, gfrag env (Intersection ys) = true -> gfrag env z = true ->
    match z with RootResolved _ _ _ | Generic _ | Nullable (RootResolved _ _ _) | Nullable (Generic _) => True | _ => False end ->
    assignable (Intersection ys) z -> exists C, In C ys /\ assignable C z.
Proof.
    intros ys z Hys Hz Hs H. pose proof (gfrag_no_vars env _ Hys) as Hvy. pose proof (gfrag_no_vars env _ Hz) as Hvz.
    destruct (assignable_takes (Intersection ys) z Hvy Hvz H) as [n Hn]. destruct n as [|n]; [discriminate (Hn [])|].
    destruct z as [m c args|zn|g|me msg|v o zn|g|zs|us]; try contradiction.
    - pose proof (Hn []) as H0. rewrite step_root_inter in H0.
      destruct (intersection_flipped_unify_found env n _ ys [] [] H0) as [C [Hc HC]]. exists C. split; [exact Hc|].
      exact (takes_assignable n C _ [] (gfrag_no_vars env C (intersection_component_gfrag ys C Hys Hc)) Hvz HC).
    - (* nullable: what it wraps takes the intersection without null, by one of its components *)
      assert (Hgzn: gfrag env zn = true) by (change (non_null env zn && gfrag env zn = true) in Hz; apply andb_true_iff in Hz; exact (proj2 Hz)).
      destruct n as [|n]; [pose proof (Hn []) as H0; rewrite (step_nullable_inter env 0 zn ys []) in H0; discriminate H0|].
      pose proof (Hn []) as H0. rewrite (step_nullable_inter env (S n) zn ys []), (without_null_intersection ys Hys) in H0.
      assert (Hfl: unify env (S n) zn (Intersection (map (without_null env) ys)) (Ongoing []) = intersection_flipped_unify (unify env n) zn (map (without_null env) ys) []).
      { destruct zn as [| | | | | | |]; try (exfalso; exact Hs); [apply step_root_inter|apply step_generic_inter]. }
      rewrite Hfl in H0. destruct (intersection_flipped_unify_found env n zn _ [] [] H0) as [C' [Hc' HC']].
      apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. exists C. split; [exact Hc|].
      pose proof (intersection_component_gfrag ys C Hys Hc) as HC. apply (below_nullable C zn HC).
      exact (takes_assignable n _ zn [] (gfrag_no_vars env _ (gfrag_without_null env wf declared declared_wf C HC)) (gfrag_no_vars env zn Hgzn) HC').
    - pose proof (Hn []) as H0. rewrite step_generic_inter in H0.
      destruct (intersection_flipped_unify_found env n _ ys [] [] H0) as [C [Hc HC]]. exists C. split; [exact Hc|].
      exact (takes_assignable n C _ [] (gfrag_no_vars env C (intersection_component_gfrag ys C Hys Hc)) Hvz HC).
Qed.

(* ... and below a nullable union likewise, the union taking the intersection without null *)
Lemma intersection_assignee_below_nullable_union: forall ys zs, gfrag env (Intersection ys) = true ->
    assignable (Intersection ys) (Nullable (Union zs)) ->
    (exists C, In C ys /\ assignable C (Nullable (Union zs))) \/ (exists y, In y zs /\ assignable (Intersection ys) (Nullable y)).
Proof.
    intros ys zs Hys H. apply (below_nullable _ _ Hys) in H. rewrite (without_null_intersection ys Hys) in H.
    destruct (intersection_assignee_below_union _ zs H) as [[C' [Hc' HC']]|[y [Hy Hu]]].
    - left. apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. exists C. split; [exact Hc|].
      apply (below_nullable C _ (intersection_component_gfrag ys C Hys Hc)). exact HC'.
    - right. exists y. split; [exact Hy|]. apply (below_nullable _ y Hys). rewrite (without_null_intersection ys Hys). exact Hu.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Transitivity                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* Where a type is assignable to another, and that one to a third, unify never rejects assigning the first to the
   third: Generics.transitivity_never_fails, with unions. The unions are taken apart (a union assignee by its
   components, a union target by the component that takes the value), the intersections and nullable types around
   them too, down to triples of gfrag *)
Theorem ugfrag_transitive_never_fails: forall x y z, ugfrag env x = true -> ugfrag env y = true -> ugfrag env z = true ->
    assignable x y -> assignable y z -> never_fails z x.
Proof.
    intros x y z. remember (esize x + esize y + esize z) as k eqn:Hk. revert x y z Hk.
    induction k as [k IH] using lt_wf_ind. intros x y z -> Hx Hy Hz Hxy Hyz.
    pose proof (ugfrag_no_vars x Hx) as Hvx. pose proof (ugfrag_no_vars y Hy) as Hvy. pose proof (ugfrag_no_vars z Hz) as Hvz.
    (* z an intersection: each of its components takes y, and never rejects x *)
    assert (HZI: forall zs, z = Intersection zs -> never_fails z x).
    { intros zs Ez. subst z.
      apply (intersection_target_never_fails zs x Hz Hvx).
      - pose proof (ugfrag_shape env x Hx) as Hs. destruct x as [|xn| | | | | |]; try contradiction; try exact I.
        cbn [inter_shape]. destruct (nullable_assignee_target xn y Hy Hxy) as [yn [Ey Hyn]]. subst y.
        exact (nullable_below_intersection yn zs Hyz).
      - intros C Hc. pose proof (esize_in zs C Hc). pose proof (intersection_component_gfrag zs C Hz Hc) as HC.
        exact (IH (esize x + esize y + esize C) ltac:(cbn [esize]; lia) x y C eq_refl Hx Hy (gfrag_ugfrag env C HC) Hxy
            (intersection_target_components zs y Hz Hy Hyz C Hc)). }
    (* z a nullable intersection: each of its components, made nullable, takes y *)
    assert (HZN: forall zs, z = Nullable (Intersection zs) -> never_fails z x).
    { intros zs Ez. subst z. pose proof (nullable_intersection_gfrag zs Hz) as Hzs.
      assert (HIH: forall C, In C zs -> never_fails (Nullable C) x).
      { intros C Hc. pose proof (esize_in zs C Hc). pose proof (nullable_component_gfrag zs C Hz Hc) as HC.
        exact (IH (esize x + esize y + esize (Nullable C)) ltac:(cbn [esize]; lia) x y (Nullable C) eq_refl Hx Hy (gfrag_ugfrag env _ HC) Hxy
            (nullable_intersection_target_components zs y Hz Hy Hyz C Hc)). }
      destruct (ugfrag_cases env x Hx) as [Gx|[[xs [Ex [_ Hxs]]]|[xs [Ex [_ Hxs]]]]].
      - exact (nullable_intersection_target_never_fails zs x Hzs Gx HIH).
      - subst x. refine (union_assignee_never_fails (Nullable (Intersection zs)) xs I Hvz (union_components_no_vars xs Hx) _).
        intros C Hc. pose proof (esize_in xs C Hc).
        exact (IH (esize C + esize y + esize (Nullable (Intersection zs))) ltac:(cbn [esize]; lia) C y _ eq_refl
            (gfrag_ugfrag env C (component_gfrag xs C Hx Hc)) Hy Hz (union_assignee_components xs y Hx Hy Hxy C Hc) Hyz).
      - subst x. destruct (nullable_assignee_target (Union xs) y Hy Hxy) as [yn [Ey Hyn]]. subst y.
        apply never_fails_step. intros n s E. rewrite unify_nullable_nullable in E.
        exact (IH (esize (Union xs) + esize yn + esize (Intersection zs)) ltac:(cbn [esize]; lia) (Union xs) yn (Intersection zs) eq_refl
            Hx (ugfrag_nullable env yn Hy) (gfrag_ugfrag env _ Hzs) Hyn (proj1 (below_nullable_nullable env yn (Intersection zs)) Hyz) n s E). }
    (* the rest: z is a class type, a reference, a union, or one of them made nullable *)
    assert (Hflat: match z with Intersection _ | Nullable (Intersection _) => False | _ => True end -> never_fails z x).
    { intros Hsz.
      destruct (ugfrag_cases env x Hx) as [Gx|[[xs [Ex [_ Hxs]]]|[xs [Ex [_ Hxs]]]]].
      2: { (* x a union: each component is below y, and never rejected by z *) subst x.
           refine (union_assignee_never_fails z xs _ Hvz (union_components_no_vars xs Hx) _).
           - pose proof (ugfrag_shape env z Hz) as Hs. destruct z as [| | | | | | |]; try contradiction; exact I.
           - intros C Hc. pose proof (esize_in xs C Hc).
             exact (IH (esize C + esize y + esize z) ltac:(cbn [esize]; lia) C y z eq_refl (gfrag_ugfrag env C (component_gfrag xs C Hx Hc)) Hy Hz
                 (union_assignee_components xs y Hx Hy Hxy C Hc) Hyz). }
      2: { (* x a nullable union: y and z are nullable, and the union is below what they wrap *) subst x.
           destruct (nullable_assignee_target (Union xs) y Hy Hxy) as [yn [Ey Hyn]]. subst y.
           destruct (nullable_assignee_target yn z Hz Hyz) as [zn [Ez Hzn]]. subst z.
           apply never_fails_step. intros n s E. rewrite unify_nullable_nullable in E.
           exact (IH (esize (Union xs) + esize yn + esize zn) ltac:(cbn [esize]; lia) (Union xs) yn zn eq_refl Hx (ugfrag_nullable env yn Hy)
               (ugfrag_nullable env zn Hz) Hyn Hzn n s E). }
      (* x of gfrag *)
      destruct (ugfrag_cases env y Hy) as [Gy|[[ys [Ey [_ Hys]]]|[ys [Ey [_ Hys]]]]].
      2: { (* y a union: x is below one of its components, or a component of x is; each is below z *) subst y.
           assert (Hcomp: forall C, In C ys -> assignable C z) by exact (union_assignee_components ys z Hy Hz Hyz).
           assert (Hvia: forall x', ugfrag env x' = true -> esize x' <= esize x -> (exists C, In C ys /\ assignable x' C) -> never_fails z x').
           { intros x' Hx' Hsize [C [Hc HC]]. pose proof (esize_in ys C Hc).
             exact (IH (esize x' + esize C + esize z) ltac:(cbn [esize]; lia) x' C z eq_refl Hx' (gfrag_ugfrag env C (component_gfrag ys C Hy Hc)) Hz HC (Hcomp C Hc)). }
           pose proof (ugfrag_shape env x Hx) as Hs.
           destruct x as [m c args|xn|g|me msg|v o xn|g|cs|us]; try contradiction.
           - exact (Hvia _ Hx (le_n _) (union_target_component ys (RootResolved m c args) I Hxy)).
           - exfalso. destruct (nullable_assignee_target xn (Union ys) Hy Hxy) as [yn [Eyn _]]. discriminate Eyn.
           - exact (Hvia _ Hx (le_n _) (union_target_component ys (Generic g) I Hxy)).
           - destruct (union_target_intersection ys cs Hy Gx Hxy) as [[y' [Hy' Hu]]|[C [y' [Hc [Hy' HC]]]]].
             + exact (Hvia _ Hx (le_n _) (ex_intro _ y' (conj Hy' Hu))).
             + pose proof (esize_in cs C Hc). pose proof (esize_in ys y' Hy'). pose proof (intersection_component_gfrag cs C Gx Hc) as HC'.
               apply (intersection_assignee_never_fails z cs C Hz Hsz Gx Hc).
               exact (IH (esize C + esize y' + esize z) ltac:(cbn [esize]; lia) C y' z eq_refl (gfrag_ugfrag env C HC')
                   (gfrag_ugfrag env y' (component_gfrag ys y' Hy Hy')) Hz HC (Hcomp y' Hy')).
           - simpl in Gx. discriminate Gx. }
      2: { (* y a nullable union: z is nullable, and x without null is below a component of y, or a component of x is *) subst y.
           destruct (nullable_assignee_target (Union ys) z Hz Hyz) as [zn [Ez Hzn]]. subst z.
           pose proof (ugfrag_nullable env zn Hz) as Hzn'.
           assert (Hcomp: forall C, In C ys -> assignable C zn) by exact (union_assignee_components ys zn Hy Hzn' Hzn).
           assert (Hvia: forall x', gfrag env x' = true -> esize x' <= esize x -> (exists C, In C ys /\ assignable (without_null env x') C) ->
               never_fails (Nullable zn) x').
           { intros x' Hx' Hsize [C [Hc HC]]. pose proof (esize_in ys C Hc).
             exact (IH (esize x' + esize (Nullable C) + esize (Nullable zn)) ltac:(cbn [esize]; lia) x' (Nullable C) (Nullable zn) eq_refl
                 (gfrag_ugfrag env x' Hx') (gfrag_ugfrag env _ (component_nullable_gfrag ys C Hy Hc)) Hz (proj2 (below_nullable x' C Hx') HC)
                 (proj2 (below_nullable_nullable env C zn) (Hcomp C Hc))). }
           pose proof (proj1 (below_nullable x (Union ys) Gx) Hxy) as Hwx.
           destruct (gfrag_cases env x Gx) as [[m [c [args Ex]]]|[[xn [Ex [Hnn Gxn]]]|[[gm [nn [p [vs [Ex _]]]]]|[cs Ex]]]]; subst x.
           - rewrite (without_null_unchanged env (RootResolved m c args) eq_refl) in Hwx. apply (Hvia _ Gx (le_n _)).
             rewrite (without_null_unchanged env (RootResolved m c args) eq_refl). exact (union_target_component ys (RootResolved m c args) I Hwx).
           - (* a nullable type: what it wraps is below the union, as a whole or by a component *)
             assert (Ew: without_null env (Nullable xn) = xn) by (cbn [without_null]; exact (without_null_unchanged env xn (non_null_not_nullable env xn Hnn))).
             rewrite Ew in Hwx. pose proof (ugfrag_shape env _ (gfrag_ugfrag env _ Gxn)) as Hs.
             destruct xn as [m c args|xn'|g|me msg|v o xn'|g|cs|us]; try contradiction.
             + apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (union_target_component ys (RootResolved m c args) I Hwx).
             + exfalso. cbn [non_null is_component] in Hnn. discriminate Hnn.
             + apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (union_target_component ys (Generic g) I Hwx).
             + destruct (union_target_intersection ys cs Hy Gxn Hwx) as [[y' [Hy' Hu]]|[C [y' [Hc [Hy' HC]]]]].
               * apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (ex_intro _ y' (conj Hy' Hu)).
               * (* a component of the intersection is below a component of the union, which is below zn *)
                 apply never_fails_step. intros n s E. rewrite unify_nullable_nullable in E.
                 assert (Hszn: match zn with Intersection _ | Nullable (Intersection _) => False | _ => True end).
                 { destruct zn as [| [| | | | | | |] | | | | | |]; try exact I; try exact Hsz; simpl in Hz; discriminate Hz. }
                 refine (intersection_assignee_never_fails zn cs C Hzn' Hszn Gxn Hc _ n s E).
                 pose proof (esize_in cs C Hc). pose proof (esize_in ys y' Hy'). pose proof (intersection_component_gfrag cs C Gxn Hc) as HC'.
                 exact (IH (esize C + esize y' + esize zn) ltac:(cbn [esize]; lia) C y' zn eq_refl (gfrag_ugfrag env C HC')
                     (gfrag_ugfrag env y' (component_gfrag ys y' Hy Hy')) Hzn' HC (Hcomp y' Hy')).
             + simpl in Gxn. discriminate Gxn.
           - apply (Hvia _ Gx (le_n _)). exact (union_target_component ys (without_null env (Generic (mkGenericRef gm nn p vs))) I Hwx).
           - (* an intersection: without null, it is below the union as a whole, or by a component *)
             rewrite (without_null_intersection cs Gx) in Hwx.
             pose proof (gfrag_without_null env wf declared declared_wf _ Gx) as Hw. rewrite (without_null_intersection cs Gx) in Hw.
             destruct (union_target_intersection ys _ Hy Hw Hwx) as [[y' [Hy' Hu]]|[C' [y' [Hc' [Hy' HC']]]]].
             + apply (Hvia _ Gx (le_n _)). exists y'. split; [exact Hy'|]. rewrite (without_null_intersection cs Gx). exact Hu.
             + apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. pose proof (esize_in cs C Hc).
               apply (intersection_assignee_never_fails (Nullable zn) cs C Hz Hsz Gx Hc).
               apply (Hvia C (intersection_component_gfrag cs C Gx Hc) ltac:(cbn [esize]; lia)). exists y'. exact (conj Hy' HC'). }
      (* x and y of gfrag *)
      destruct (ugfrag_cases env z Hz) as [Gz|[[zs [Ez [_ Hzs]]]|[zs [Ez [_ Hzs]]]]].
      - (* all three of the fragment of type parameters and intersections: Generics.v *)
        destruct Hxy as [n1 H1]. destruct Hyz as [n2 H2].
        exact (never_fails_of_answers z x Hvz Hvx (transitivity_never_fails env wf declared declared_wf n1 n2 x y z Gx Gy Gz I I I H1 H2)).
      - (* z a union: y, or a component of it, is below a component of z *) subst z.
        assert (Hfx: flat x).
        { pose proof (ugfrag_shape env x Hx) as Hs. destruct x as [|xn| | | | | |]; try contradiction; try exact I.
          - exfalso. destruct (nullable_assignee_target xn y Hy Hxy) as [yn [Eyn _]]. subst y.
            destruct (nullable_assignee_target yn (Union zs) Hz Hyz) as [zn [Ezn _]]. discriminate Ezn.
          - simpl in Gx. discriminate Gx. }
        assert (Hvia: forall y', ugfrag env y' = true -> esize y' <= esize y -> assignable x y' -> (exists C, In C zs /\ assignable y' C) ->
            never_fails (Union zs) x).
        { intros y' Hy' Hsize Hxy' [C [Hc HC]]. pose proof (esize_in zs C Hc).
          apply (union_target_never_fails zs x C (union_components_no_vars zs Hz) Hc Hfx).
          exact (IH (esize x + esize y' + esize C) ltac:(cbn [esize]; lia) x y' C eq_refl Hx Hy' (gfrag_ugfrag env C (component_gfrag zs C Hz Hc)) Hxy' HC). }
        destruct (gfrag_cases env y Gy) as [[m [c [args Ey]]]|[[yn [Ey [Hnn Gyn]]]|[[gm [nn [p [vs [Ey _]]]]]|[ys Ey]]]]; subst y.
        + exact (Hvia _ Hy (le_n _) Hxy (union_target_component zs (RootResolved m c args) I Hyz)).
        + exfalso. destruct (nullable_assignee_target yn (Union zs) Hz Hyz) as [zn [Ezn _]]. discriminate Ezn.
        + exact (Hvia _ Hy (le_n _) Hxy (union_target_component zs (Generic (mkGenericRef gm nn p vs)) I Hyz)).
        + destruct (intersection_assignee_below_union ys zs Hyz) as [[C [Hc HC]]|[y' [Hy' Hu]]].
          * pose proof (esize_in ys C Hc). pose proof (intersection_component_gfrag ys C Gy Hc) as HC'.
            exact (IH (esize x + esize C + esize (Union zs)) ltac:(cbn [esize]; lia) x C (Union zs) eq_refl Hx (gfrag_ugfrag env C HC') Hz
                (intersection_target_components ys x Gy Hx Hxy C Hc) HC).
          * exact (Hvia _ Hy (le_n _) Hxy (ex_intro _ y' (conj Hy' Hu))).
      - (* z a nullable union: y without null is below a component of z, as a whole or by a component *) subst z.
        apply (nullable_target_never_fails (Union zs) x Gx).
        assert (Hfw: flat (without_null env x)).
        { pose proof (without_null_shape env x) as Hs. pose proof (gfrag_without_null env wf declared declared_wf x Gx) as Hw.
          remember (without_null env x) as w eqn:Ew. destruct w as [| | | | | | |]; try exact I; try contradiction; simpl in Hw; discriminate Hw. }
        assert (Hvia: forall y', gfrag env y' = true -> esize y' <= esize y -> assignable x y' -> (exists C, In C zs /\ assignable (without_null env y') C) ->
            never_fails (Union zs) (without_null env x)).
        { intros y' Hy' Hsize Hxy' [C [Hc HC]]. pose proof (esize_in zs C Hc).
          apply (union_target_never_fails zs _ C (union_components_no_vars zs Hz) Hc Hfw).
          apply (nullable_target_strip C x Gx).
          exact (IH (esize x + esize y' + esize (Nullable C)) ltac:(cbn [esize]; lia) x y' (Nullable C) eq_refl Hx (gfrag_ugfrag env y' Hy')
              (gfrag_ugfrag env _ (component_nullable_gfrag zs C Hz Hc)) Hxy' (proj2 (below_nullable y' C Hy') HC)). }
        pose proof (proj1 (below_nullable y (Union zs) Gy) Hyz) as Hwy.
        destruct (gfrag_cases env y Gy) as [[m [c [args Ey]]]|[[yn [Ey [Hnn Gyn]]]|[[gm [nn [p [vs [Ey _]]]]]|[ys Ey]]]]; subst y.
        + rewrite (without_null_unchanged env (RootResolved m c args) eq_refl) in Hwy. apply (Hvia _ Gy (le_n _) Hxy).
          rewrite (without_null_unchanged env (RootResolved m c args) eq_refl). exact (union_target_component zs (RootResolved m c args) I Hwy).
        + (* a nullable type: what it wraps is below the union *)
          assert (Ew: without_null env (Nullable yn) = yn) by (cbn [without_null]; exact (without_null_unchanged env yn (non_null_not_nullable env yn Hnn))).
          rewrite Ew in Hwy. pose proof (ugfrag_shape env _ (gfrag_ugfrag env _ Gyn)) as Hs.
          destruct yn as [m c args|yn'|g|me msg|v o yn'|g|ys|us]; try contradiction.
          * apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (union_target_component zs (RootResolved m c args) I Hwy).
          * exfalso. cbn [non_null is_component] in Hnn. discriminate Hnn.
          * apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (union_target_component zs (Generic g) I Hwy).
          * destruct (intersection_assignee_below_union ys zs Hwy) as [[C [Hc HC]]|[y' [Hy' Hu]]].
            { (* x is below the component made nullable, which is below z *)
              pose proof (esize_in ys C Hc). pose proof (nullable_component_gfrag ys C Gy Hc) as HC'.
              apply (nullable_target_strip (Union zs) x Gx).
              exact (IH (esize x + esize (Nullable C) + esize (Nullable (Union zs))) ltac:(cbn [esize]; lia) x (Nullable C) (Nullable (Union zs)) eq_refl
                  Hx (gfrag_ugfrag env _ HC') Hz (nullable_intersection_target_components ys x Gy Hx Hxy C Hc)
                  (proj2 (below_nullable_nullable env C (Union zs)) HC)). }
            { apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (ex_intro _ y' (conj Hy' Hu)). }
          * simpl in Gyn. discriminate Gyn.
        + apply (Hvia _ Gy (le_n _) Hxy). exact (union_target_component zs (without_null env (Generic (mkGenericRef gm nn p vs))) I Hwy).
        + (* an intersection: a component of it is below z, or a component of z takes it without null *)
          rewrite (without_null_intersection ys Gy) in Hwy.
          destruct (intersection_assignee_below_union _ zs Hwy) as [[C' [Hc' HC']]|[y' [Hy' Hu]]].
          * apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. pose proof (esize_in ys C Hc). pose proof (intersection_component_gfrag ys C Gy Hc) as HC.
            apply (nullable_target_strip (Union zs) x Gx).
            exact (IH (esize x + esize C + esize (Nullable (Union zs))) ltac:(cbn [esize]; lia) x C (Nullable (Union zs)) eq_refl Hx (gfrag_ugfrag env C HC) Hz
                (intersection_target_components ys x Gy Hx Hxy C Hc) (proj2 (below_nullable C (Union zs) HC) HC')).
          * apply (Hvia _ Gy (le_n _) Hxy). exists y'. split; [exact Hy'|]. rewrite (without_null_intersection ys Gy). exact Hu. }
    pose proof (ugfrag_shape env z Hz) as Hsz.
    destruct z as [mz cz zargs|zn|gz|me msg|v o zn|g|zs|zs]; try contradiction; try (apply Hflat; exact I); [|exact (HZI zs eq_refl)].
    destruct zn as [m c args|zn'|g|me msg|v o zn'|g|zs|zs]; try (apply Hflat; exact I). exact (HZN zs eq_refl).
Qed.

(* As Generics.transitivity_never_fails states it *)
Theorem transitivity_never_fails_with_unions: forall n1 n2 x y z,
    ugfrag env x = true -> ugfrag env y = true -> ugfrag env z = true ->
    refs_wf env declared x -> refs_wf env declared y -> refs_wf env declared z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    forall n3, is_assignable_to env n3 x z <> Some false.
Proof.
    intros n1 n2 x y z Hx Hy Hz _ _ _ H1 H2 n3 E.
    pose proof (ugfrag_transitive_never_fails x y z Hx Hy Hz (ex_intro _ n1 H1) (ex_intro _ n2 H2)) as Hnf.
    unfold is_assignable_to, empty_unification in E.
    destruct (unify env n3 z x (Ongoing [])) as [[u|]|] eqn:E'; simpl in E; try discriminate E. exact (Hnf n3 [] E').
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Termination, and transitivity as usual                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma list_sum_map_le: forall {T: Type} (f0 f1: T -> nat) (l: list T), (forall x, In x l -> f0 x <= f1 x) ->
    list_sum (map f0 l) <= list_sum (map f1 l).
Proof.
    intros T f0 f1 l H. induction l as [|x l IH]; [reflexivity|]. simpl. pose proof (H x (or_introl eq_refl)).
    assert (list_sum (map f0 l) <= list_sum (map f1 l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma esize_without_null: forall t, esize (without_null env t) <= esize t.
Proof.
    intros t. remember (esize t) as k eqn:Hk. revert t Hk. induction k as [k IH] using lt_wf_ind. intros t ->.
    destruct t as [m c args|n|[gm nn p vs]|me msg|v o n|g|cs|us]; cbn [without_null esize]; try lia.
    - pose proof (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl). lia.
    - pose proof (IH (esize n) ltac:(cbn [esize]; lia) n eq_refl). cbn [esize]. lia.
    - destruct (forallb (is_nullable env) cs); cbn [esize]; [|lia].
      assert (list_sum (map esize (map (without_null env) cs)) <= list_sum (map esize cs)).
      { rewrite map_map. apply list_sum_map_le. intros x Hx. pose proof (esize_in cs x Hx). exact (IH (esize x) ltac:(cbn [esize]; lia) x eq_refl). }
      lia.
    - assert (list_sum (map esize (map (without_null env) us)) <= list_sum (map esize us)).
      { rewrite map_map. apply list_sum_map_le. intros x Hx. pose proof (esize_in us x Hx). exact (IH (esize x) ltac:(cbn [esize]; lia) x eq_refl). }
      lia.
Qed.

Lemma kugfrag_no_vars: forall t, kugfrag env t = true -> no_vars t = true.
Proof.
    intros t H. destruct (kugfrag_cases env t H) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]]; [exact (gfrag_no_vars env t Hg)| |];
        cbn [no_vars]; apply forallb_forall; intros C Hc; exact (gfrag_no_vars env C (kept_union_component_gfrag env C (Hus C Hc))).
Qed.

Lemma kcomponents_no_vars: forall us, kugfrag env (Union us) = true -> forallb no_vars us = true.
Proof. intros us H. exact (kugfrag_no_vars (Union us) H). Qed.

Lemma kcomponent_gfrag: forall us C, kugfrag env (Union us) = true -> In C us -> gfrag env C = true.
Proof. intros us C H Hc. exact (kept_union_component_gfrag env C (proj2 (kugfrag_union env us H) C Hc)). Qed.

(* Unify terminates on the types of the fragment of type parameters and intersections, in the environment at hand
   (Conjectures.unify_terminates_on): the premise of the theorems that an assignment is accepted *)
Hypothesis terminates: unify_terminates_on env declared.

Let answers (t a: EType): Prop := exists n, unify env n t a (Ongoing []) <> None.

Lemma gfrag_answers: forall t a, gfrag env t = true -> gfrag env a = true -> answers t a.
Proof. intros t a Ht Ha. exact (terminates wf declared_wf t a [] Ht Ha I I). Qed.

Lemma answers_free: forall n t a s, no_vars t = true -> no_vars a = true ->
    unify env n t a (Ongoing []) <> None -> unify env n t a (Ongoing s) <> None.
Proof.
    intros n t a s Ht Ha H E. destruct (unify env n t a (Ongoing [])) as [u|] eqn:E0; [|exact (H eq_refl)].
    rewrite (unify_free env wf n t a [] s u Ht Ha E0) in E. discriminate E.
Qed.

Lemma fold_targets_answers: forall n a cs s, no_vars a = true -> forallb no_vars cs = true ->
    (forall C, In C cs -> unify env n C a (Ongoing s) <> None) ->
    fold_unify (fun inner C => unify env n C a inner) cs (Ongoing s) <> None.
Proof.
    intros n a cs s Ha Hcs H. induction cs as [|C cs IH]; [discriminate|]. simpl in Hcs |- *. apply andb_true_iff in Hcs.
    destruct (unify env n C a (Ongoing s)) as [[s'|]|] eqn:E.
    - rewrite (keeps_states env wf n C a s s' (proj1 Hcs) Ha E). apply IH; [exact (proj2 Hcs)|]. intros C' Hc. apply H. right. exact Hc.
    - rewrite fold_unify_stays_failed. discriminate.
    - exfalso. exact (H C (or_introl eq_refl) E).
Qed.

(* An intersection as the target answers where each of its components does *)
Lemma inter_target_answers: forall n cs a, forallb no_vars cs = true -> no_vars a = true -> inter_shape env cs a ->
    (forall C, In C cs -> unify env n C a (Ongoing []) <> None) -> unify env (S n) (Intersection cs) a (Ongoing []) <> None.
Proof.
    intros n cs a Hcs Ha Hs H E. apply (inter_body env n cs a [] _ Hs) in E. unfold intersection_body in E.
    destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar]. cbn zeta in E. rewrite Hvar, Hnonvar in E.
    destruct (fold_unify (fun inner C => unify env n C a inner) cs (Ongoing [])) as [[s2|]|] eqn:F;
        [|discriminate E|exact (fold_targets_answers n a cs [] Ha Hcs H F)].
    match type of E with context [find_first ?f cs] => destruct (find_first f cs) as [[[C0 s3]|]|] eqn:F2 end; try discriminate E.
    rewrite forallb_forall in Hcs.
    exact (find_first_answers (fun C => unify env n C a (Ongoing s2)) cs (fun C Hc => answers_free n C a s2 (Hcs C Hc) Ha (H C Hc)) F2).
Qed.

(* Then unify terminates on the fragment with unions, too: the components are tried one by one *)
Theorem kugfrag_terminates: forall t a, kugfrag env t = true -> kugfrag env a = true -> answers t a.
Proof.
    intros t a. remember (esize t + esize a) as k eqn:Hk. revert t a Hk. induction k as [k IH] using lt_wf_ind. intros t a -> Ht Ha.
    pose proof (kugfrag_no_vars t Ht) as Hvt. pose proof (kugfrag_no_vars a Ha) as Hva.
    (* a union assignee, to a target that is no intersection: each component, with fuel for all of them *)
    assert (Hflip: forall us, kugfrag env (Union us) = true -> esize (Union us) <= esize a ->
        match t with RootResolved _ _ _ | Nullable _ | Generic _ | Union _ => True | _ => False end -> answers t (Union us)).
    { intros us Hus Hsz Hst. pose proof (kcomponents_no_vars us Hus) as Hvus.
      destruct (fuel_for_all (fun n C => unify env n t C (Ongoing []) <> None) us) as [n Hn].
      - intros n n' C Hle H. exact (answers_mono env n n' t C [] Hle H).
      - intros C Hc. pose proof (esize_in us C Hc).
        exact (IH (esize t + esize C) ltac:(cbn [esize] in Hsz; lia) t C eq_refl Ht (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc))).
      - exists (S n). rewrite (step_union_assignee n t us [] Hst). exact (fold_answers env wf n t us [] Hvt Hvus Hn). }
    (* a union target, and an assignee that is a type of values: the first component that takes it *)
    assert (Hsearch: forall us, kugfrag env (Union us) = true -> esize (Union us) <= esize t ->
        match a with RootResolved _ _ _ | Nullable _ | Generic _ => True | _ => False end -> answers (Union us) a).
    { intros us Hus Hsz Hsa. pose proof (kcomponents_no_vars us Hus) as Hvus.
      destruct (fuel_for_all (fun n C => unify env n C a (Ongoing []) <> None) us) as [n Hn].
      - intros n n' C Hle H. exact (answers_mono env n n' C a [] Hle H).
      - intros C Hc. pose proof (esize_in us C Hc).
        exact (IH (esize C + esize a) ltac:(cbn [esize] in Hsz; lia) C a eq_refl (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc)) Ha).
      - exists (S n). rewrite (step_union_target n us a [] Hsa). unfold union_body.
        destruct (no_vars_filter us Hvus) as [Hvar Hnonvar]. cbn zeta. rewrite Hvar, Hnonvar, app_nil_r.
        destruct (find_first _ us) as [[[C s']|]|] eqn:E; [discriminate|discriminate|].
        exfalso. exact (find_first_answers (fun C => unify env n C a (Ongoing [])) us Hn E). }
    (* ... and an intersection assignee: its components against the union, then the union's against it *)
    assert (Hinter: forall us cs, kugfrag env (Union us) = true -> esize (Union us) <= esize t ->
        gfrag env (Intersection cs) = true -> esize (Intersection cs) <= esize a -> answers (Union us) (Intersection cs)).
    { intros us cs Hus Hsz Hcs Hsza. pose proof (kcomponents_no_vars us Hus) as Hvus.
      destruct (fuel_for_all (fun n C => unify env n (Union us) C (Ongoing []) <> None) cs) as [n0 Hn0].
      - intros n n' C Hle H. exact (answers_mono env n n' (Union us) C [] Hle H).
      - intros C Hc. pose proof (esize_in cs C Hc).
        exact (IH (esize (Union us) + esize C) ltac:(cbn [esize] in Hsza; lia) (Union us) C eq_refl Hus
            (gfrag_kugfrag env C (intersection_component_gfrag cs C Hcs Hc))).
      - destruct (fuel_for_all (fun n C => unify env n C (Intersection cs) (Ongoing []) <> None) us) as [n1 Hn1].
        + intros n n' C Hle H. exact (answers_mono env n n' C (Intersection cs) [] Hle H).
        + intros C Hc. pose proof (esize_in us C Hc).
          exact (IH (esize C + esize (Intersection cs)) ltac:(cbn [esize] in Hsz; lia) C (Intersection cs) eq_refl
              (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc)) (gfrag_kugfrag env _ Hcs)).
        + exists (S (max n0 n1)). rewrite step_union_intersection.
          assert (Hfl: intersection_flipped_unify (unify env (max n0 n1)) (Union us) cs [] <> None).
          { unfold intersection_flipped_unify. destruct (find_first _ cs) as [[[C s']|]|] eqn:E; [discriminate|discriminate|].
            exfalso. apply (find_first_answers (fun C => unify env (max n0 n1) (Union us) C (Ongoing [])) cs); [|exact E].
            intros C Hc. apply (answers_mono env n0 (max n0 n1)); [lia|exact (Hn0 C Hc)]. }
          destruct (intersection_flipped_unify (unify env (max n0 n1)) (Union us) cs []) as [[s'|]|]; [discriminate| |exfalso; exact (Hfl eq_refl)].
          unfold union_body. destruct (no_vars_filter us Hvus) as [Hvar Hnonvar]. cbn zeta. rewrite Hvar, Hnonvar, app_nil_r.
          destruct (find_first _ us) as [[[C s']|]|] eqn:E; [discriminate|discriminate|].
          exfalso. apply (find_first_answers (fun C => unify env (max n0 n1) C (Intersection cs) (Ongoing [])) us); [|exact E].
          intros C Hc. apply (answers_mono env n1 (max n0 n1)); [lia|exact (Hn1 C Hc)]. }
    destruct (kugfrag_cases env t Ht) as [Gt|[[ts [-> [_ Hts]]]|[ts [-> [_ Hts]]]]].
    - (* t of gfrag *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + exact (gfrag_answers t a Gt Ga).
      + (* a union assignee *)
        destruct (gfrag_cases env t Gt) as [[m [c [args Et]]]|[[tn [Et _]]|[[gm [nn [p [vs [Et _]]]]]|[cs Et]]]]; subst t;
            try (apply (Hflip ys Ha (le_n _)); exact I).
        (* an intersection target: each of its components *)
        destruct (fuel_for_all (fun n C => unify env n C (Union ys) (Ongoing []) <> None) cs) as [n Hn].
        * intros n n' C Hle H. exact (answers_mono env n n' C (Union ys) [] Hle H).
        * intros C Hc. pose proof (esize_in cs C Hc).
          exact (IH (esize C + esize (Union ys)) ltac:(cbn [esize] in *; lia) C (Union ys) eq_refl (gfrag_kugfrag env C (intersection_component_gfrag cs C Gt Hc)) Ha).
        * exists (S n). exact (inter_target_answers n cs (Union ys) (gfrag_components_no_vars env cs Gt) Hva I Hn).
      + (* a nullable union assignee: rejected, or taken by what the target wraps *)
        destruct (gfrag_cases env t Gt) as [[m [c [args Et]]]|[[tn [Et [Hnn Gtn]]]|[[gm [nn [p [vs [Et _]]]]]|[cs Et]]]]; subst t.
        * exists 1. discriminate.
        * destruct (IH (esize tn + esize (Union ys)) ltac:(cbn [esize] in *; lia) tn (Union ys) eq_refl (gfrag_kugfrag env tn Gtn) Ha) as [n Hn].
          exists (S n). rewrite unify_nullable_nullable. exact Hn.
        * exists 1. rewrite step_generic_nullable. discriminate.
        * destruct (is_nullable env (Intersection cs)) eqn:En; [|exists 1; rewrite (step_inter_nullable env 0 cs _ [] En); discriminate].
          destruct (fuel_for_all (fun n C => unify env n C (Nullable (Union ys)) (Ongoing []) <> None) cs) as [n Hn].
          { intros n n' C Hle H. exact (answers_mono env n n' C _ [] Hle H). }
          { intros C Hc. pose proof (intersection_component_shape cs C Gt Hc) as Hsh. pose proof (esize_in cs C Hc).
            destruct C as [m c args|cn|g|me msg|v o cn|g|cs'|us]; try contradiction.
            - exists 1. discriminate.
            - destruct (IH (esize cn + esize (Union ys)) ltac:(cbn [esize] in *; lia) cn (Union ys) eq_refl
                  (gfrag_kugfrag env cn (gfrag_nullable_inner env cn (intersection_component_gfrag cs _ Gt Hc))) Ha) as [n Hn].
              exists (S n). rewrite unify_nullable_nullable. exact Hn.
            - exists 1. rewrite step_generic_nullable. discriminate. }
          { exists (S n). apply (inter_target_answers n cs _ (gfrag_components_no_vars env cs Gt) Hva); [exact En|exact Hn]. }
    - (* t a union *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + destruct (gfrag_cases env a Ga) as [[m [c [args Ea]]]|[[an [Ea _]]|[[gm [nn [p [vs [Ea _]]]]]|[cs Ea]]]]; subst a;
            try (apply (Hsearch ts Ht (le_n _)); exact I).
        exact (Hinter ts cs Ht (le_n _) Ga (le_n _)).
      + apply (Hflip ys Ha (le_n _)). exact I.
      + apply (Hsearch ts Ht (le_n _)). exact I.
    - (* t a nullable union: the union takes the assignee without null *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + pose proof (esize_without_null a) as Hsz.
        destruct (IH (esize (Union ts) + esize (without_null env a)) ltac:(cbn [esize] in *; lia) (Union ts) (without_null env a) eq_refl Ht
            (gfrag_kugfrag env _ (gfrag_without_null env wf declared declared_wf a Ga))) as [n Hn].
        exists (S n). rewrite (step_nullable_any env n (Union ts) a [] Ga). exact Hn.
      + apply (Hflip ys Ha (le_n _)). exact I.
      + destruct (IH (esize (Union ts) + esize (Union ys)) ltac:(cbn [esize] in *; lia) (Union ts) (Union ys) eq_refl Ht Ha) as [n Hn].
        exists (S n). rewrite unify_nullable_nullable. exact Hn.
Qed.

(* Transitivity, as usual, where unify terminates (Conjectures.transitivity_terminating, with unions) *)
Theorem transitivity_terminating_with_unions: forall n1 n2 x y z,
    ugfrag env x = true -> ugfrag env y = true -> ugfrag env z = true ->
    refs_wf env declared x -> refs_wf env declared y -> refs_wf env declared z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    exists n, is_assignable_to env n x z = Some true.
Proof.
    intros n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2.
    destruct (kugfrag_terminates z x (ugfrag_kugfrag env z Hz) (ugfrag_kugfrag env x Hx)) as [n Hf]. exists n.
    pose proof (transitivity_never_fails_with_unions n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2 n) as Hnf.
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env n z x (Ongoing [])) as [[u|]|]; simpl in *; [reflexivity|contradiction Hnf; reflexivity|contradiction Hf; reflexivity].
Qed.

End UnionsInGenericCode.

(* The premise of the theorems of the first section, from the conjecture of Conjectures.v: where unify terminates
   on the fragment of type parameters and intersections, it does on the class types *)
Lemma terminates_on_classes: forall env declared, wellformed env -> bounds_wellformed env declared ->
    unify_terminates_on env declared ->
    forall t a, in_fragment env t = true -> in_fragment env a = true -> exists n, unify env n t a (Ongoing []) <> None.
Proof.
    intros env declared wf Hb Hc t a Ht Ha. apply (Hc wf Hb t a []); try exact I; apply in_fragment_is_gfrag; assumption.
Qed.

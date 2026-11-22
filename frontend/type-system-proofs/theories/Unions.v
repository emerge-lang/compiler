(*
 * Union types, `A | B`: a value of the union is a value of one of the components. The frontend has
 * no union types yet (roadmap: union types); this is the model to build them against, and what unify
 * decides of them on the class fragment of Transitivity.v and unions of its types, nullable or not
 * (ufrag):
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

(* The premise of the theorems above, from the conjecture of Conjectures.v: where unify terminates
   on the fragment of type parameters and intersections, it does on the class types *)
Lemma terminates_on_classes: forall env declared, wellformed env -> bounds_wellformed env declared ->
    unify_terminates_on env declared ->
    forall t a, in_fragment env t = true -> in_fragment env a = true -> exists n, unify env n t a (Ongoing []) <> None.
Proof.
    intros env declared wf Hb Hc t a Ht Ha. apply (Hc wf Hb t a []); try exact I; apply in_fragment_is_gfrag; assumption.
Qed.

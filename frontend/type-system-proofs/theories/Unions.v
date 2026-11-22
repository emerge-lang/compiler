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
 * takes a class type or a reference with one of its components (Rules.union_target_component) and
 * an intersection as a whole or by a component of it (union_target_intersection), and unify never
 * rejects what transitivity says it should take (transitivity_never_fails_with_unions, from
 * Generics.transitivity_never_fails); where unify terminates on gfrag, it does on the fragment with
 * unions, components that keep their nullability included (kugfrag_terminates), and transitivity
 * is as usual (transitivity_terminating_with_unions).
 *
 * All of it is in the terms of Closed.v, and reasons by the rules of unify of Rules.v: what is left
 * here is what the fragments add, the shapes of their types and of the components.
 *)

From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Closed.
From EmergeTypeSystem Require Import Rules.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

Section Unions.

Variable env: Environment.
Hypothesis wf: wellformed env.

Let assignable := Closed.assignable env.
Let answers := Closed.answers env.

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

(* ... and as the targets of a union assignee: none an intersection *)
Lemma ufrag_takes_unions: forall t, ufrag t = true -> takes_unions t.
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
(* What unify decides of unions                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* A union assignee is taken exactly where each of its components is: `A | B` is below z iff A and B are *)
Theorem union_below_iff: forall us z, ufrag (Union us) = true -> ufrag z = true ->
    assignable (Union us) z <-> forall C, In C us -> assignable C z.
Proof.
    intros us z Hus Hz. pose proof (ufrag_takes_unions z Hz) as Hsz. pose proof (ufrag_no_vars z Hz) as Hvz. pose proof (components_no_vars us Hus) as Hvus.
    split; [exact (union_assignee_components env wf z us Hvz Hvus Hsz)|exact (union_assignee_taken env wf z us Hvz Hvus Hsz)].
Qed.

(* A union target takes a value with one of its components: a value of `A | B` is an A or a B. That
   holds of every assignee that is a type of values, not only those of the fragment *)
Theorem union_takes_component: forall us x,
    match x with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    assignable x (Union us) -> exists C, In C us /\ assignable x C.
Proof.
    intros us x Hsx [n H]. destruct n as [|n]; [discriminate H|]. rewrite assignable_step in H.
    assert (E: unify_step env (unify env n) (Union us) x [] = union_body (unify env n) us x [])
        by (destruct x as [| | |me msg| |g| |]; try contradiction; try reflexivity; destruct g; reflexivity).
    rewrite E in H. unfold verdict, option_map in H. destruct (union_body (unify env n) us x []) as [[s'|]|] eqn:Eb; try discriminate H.
    destruct (union_body_found env n us x [] s' Eb) as [C [Hc HC]]. exists C. split; [exact Hc|]. exists n.
    unfold is_assignable_to, empty_unification. rewrite HC. reflexivity.
Qed.

(* The same through a nullable union: a value of `(A | B)?` that isn't null is an A or a B *)
Theorem nullable_union_takes_component: forall us x, in_fragment env x = true ->
    assignable x (Nullable (Union us)) -> exists C, In C us /\ assignable x (Nullable C).
Proof.
    intros us x Hx [n H]. destruct n as [|n]; [discriminate H|].
    (* a value of a class type, or one that may be null: the union takes the value *)
    destruct (fragment_cases env x Hx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]];
        destruct (union_takes_component us (RootResolved m c args) I (ex_intro _ n H)) as [C [Hc [n0 HC]]];
        exists C; (split; [exact Hc|exists (S n0); exact HC]).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Termination, reflexivity and transitivity on the fragment                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* Unify terminates on the class types of the program: as Generics.v takes it of the fragment of type
   parameters and intersections (Conjectures.unify_terminates_on), from which it follows *)
Hypothesis terminates: forall t a, in_fragment env t = true -> in_fragment env a = true ->
    exists n, unify env n t a (Ongoing []) <> None.

Lemma terminates_answers: forall t a, in_fragment env t = true -> in_fragment env a = true -> answers t a.
Proof.
    intros t a Ht Ha. destruct (terminates t a Ht Ha) as [n H]. exists n. unfold is_assignable_to, empty_unification.
    destruct (unify env n t a (Ongoing [])); [discriminate|exfalso; exact (H eq_refl)].
Qed.

(* Then it terminates on the fragment of unions, too: the components are tried one by one *)
Lemma ufrag_terminates: forall t a, ufrag t = true -> ufrag a = true -> answers t a.
Proof.
    intros t a. remember (esize t + esize a) as k eqn:Hk. revert t a Hk. induction k as [k IH] using lt_wf_ind. intros t a -> Ht Ha.
    pose proof (ufrag_no_vars t Ht) as Hvt. pose proof (ufrag_no_vars a Ha) as Hva.
    (* a union assignee: each component *)
    assert (Hflip: forall us, ufrag (Union us) = true -> esize (Union us) <= esize a -> answers t (Union us)).
    { intros us Hus Hsz. apply (union_assignee_answers env wf t us Hvt (components_no_vars us Hus) (ufrag_takes_unions t Ht)).
      intros C Hc. pose proof (esize_in us C Hc). exact (IH (esize t + esize C) ltac:(cbn [esize] in Hsz; lia) t C eq_refl Ht (ufrag_components us Hus C Hc)). }
    (* a union target, and an assignee that is a type of values: the first component that takes it *)
    assert (Hsearch: forall us, ufrag (Union us) = true -> esize (Union us) <= esize t -> searched_in_unions a -> answers (Union us) a).
    { intros us Hus Hsz Hsa. apply (union_target_answers env wf us a (components_no_vars us Hus) Hva Hsa).
      intros C Hc. pose proof (esize_in us C Hc). exact (IH (esize C + esize a) ltac:(cbn [esize] in Hsz; lia) C a eq_refl (ufrag_components us Hus C Hc) Ha). }
    destruct (ufrag_cases t Ht) as [Hft|[[us [-> [Hne Hus]]]|[us [-> [Hne Hus]]]]];
        destruct (ufrag_cases a Ha) as [Hfa|[[zs [-> [Hnea Has]]]|[zs [-> [Hnea Has]]]]].
    - exact (terminates_answers t a Hft Hfa).
    - exact (Hflip zs Ha (le_n _)).
    - (* a class type, nullable or not, and a nullable union: a non-null class type rejects it, what a nullable one wraps takes the union *)
      destruct (fragment_cases env t Hft) as [[m [c [args ->]]]|[m [c [args [-> Hf']]]]]; [exists 1; discriminate|].
      destruct (IH (esize (RootResolved m c args) + esize (Union zs)) ltac:(cbn [esize]; lia) (RootResolved m c args) (Union zs) eq_refl Hf' Ha) as [n Hn].
      exists (S n). exact Hn.
    - apply (Hsearch us Ht (le_n _)). destruct (fragment_cases env a Hfa) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact I.
    - exact (Hflip zs Ha (le_n _)).
    - exact (Hsearch us Ht (le_n _) I).
    - (* a nullable union, and a class type: the union takes what it is, or wraps *)
      destruct (fragment_cases env a Hfa) as [[m [c [args ->]]]|[m [c [args [-> Hf']]]]].
      + destruct (IH (esize (Union us) + esize (RootResolved m c args)) ltac:(cbn [esize]; lia) (Union us) (RootResolved m c args) eq_refl Ht Ha) as [n Hn].
        exists (S n). exact Hn.
      + destruct (IH (esize (Union us) + esize (RootResolved m c args)) ltac:(cbn [esize]; lia) (Union us) (RootResolved m c args) eq_refl Ht Hf') as [n Hn].
        exists (S n). exact Hn.
    - exact (Hflip zs Ha (le_n _)).
    - destruct (IH (esize (Union us) + esize (Union zs)) ltac:(cbn [esize]; lia) (Union us) (Union zs) eq_refl Ht Ha) as [n Hn].
      exists (S n). exact Hn.
Qed.

(* What is below a component is below the union *)
Lemma below_union_of_component: forall x us C, ufrag x = true -> ufrag (Union us) = true -> In C us ->
    assignable x C -> assignable x (Union us).
Proof.
    intros x. remember (esize x) as k eqn:Hk. revert x Hk. induction k as [k IH] using lt_wf_ind. intros x -> us C Hx Hus Hc HxC.
    pose proof (components_no_vars us Hus) as Hvus. pose proof (ufrag_no_vars x Hx) as Hvx.
    destruct (ufrag_cases x Hx) as [Hfx|[[xs [Ex [Hne Hxs]]]|[xs [Ex [Hne Hxs]]]]].
    (* a value of a type that is no union: the first component that takes it, where all answer *)
    1, 3: apply (union_target_takes env wf us x C Hvus Hvx); [| |exact Hc|exact HxC];
          [first [destruct (fragment_cases env x Hfx) as [[m [c [args ->]]]|[m [c [args [-> _]]]]]; exact I|rewrite Ex; exact I]|];
          intros C' Hc'; exact (ufrag_terminates C' x (ufrag_components us Hus C' Hc') Hx).
    (* a union: each of its components is below C, so below the union *)
    subst x. apply (union_below_iff xs (Union us) Hx Hus). intros D Hd. pose proof (esize_in xs D Hd).
    apply (IH (esize D) ltac:(cbn [esize]; lia) D eq_refl us C (Hxs D Hd) Hus Hc).
    exact (proj1 (union_below_iff xs C Hx (ufrag_components us Hus C Hc)) HxC D Hd).
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

(* So `(A | B) & C` is below `A | B` on the fragment: the union is one of the components, every value of the
   intersection a value of it (Rules.intersection_below_union_by_component), and the components before it answer *)
Theorem intersection_with_union_below_union: forall cs us, ufrag (Union us) = true -> (forall y, In y cs -> ufrag y = true) ->
    In (Union us) cs -> assignable (Intersection cs) (Union us).
Proof.
    intros cs us Hus Hcs Hin. apply (intersection_below_union_by_component env wf us cs (Union us) (components_no_vars us Hus)).
    - apply forallb_forall. intros y Hy. exact (ufrag_no_vars y (Hcs y Hy)).
    - intros y Hy. exact (ufrag_terminates (Union us) y Hus (Hcs y Hy)).
    - exact Hin.
    - exact (ufrag_reflexive (Union us) Hus).
Qed.

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
    all: try (subst y; destruct (union_takes_component ys x Hsx Hxy) as [C [Hc HxC]]; pose proof (esize_in ys C Hc);
              apply (IH (esize x + esize C + esize z) ltac:(cbn [esize]; lia) x C z eq_refl Hx (Hys C Hc) Hz HxC);
              exact (proj1 (union_below_iff ys z Hy Hz) Hyz C Hc)).
    all: assert (Hsy: match y with Union _ | Intersection _ | TypeVariable _ | Error _ _ => False | _ => True end)
        by (first [destruct (fragment_cases env y Hfy) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; exact I|rewrite Ey; exact I]).
    (* z a union: one of its components takes y, and so x *)
    all: destruct (ufrag_cases z Hz) as [Hfz|[[zs [Ez [Hnez Hzs]]]|[zs [Ez [Hnez Hzs]]]]].
    all: try (subst z; destruct (union_takes_component zs y Hsy Hyz) as [C [Hc HyC]]; pose proof (esize_in zs C Hc);
              apply (below_union_of_component x zs C Hx Hz Hc);
              exact (IH (esize x + esize y + esize C) ltac:(cbn [esize]; lia) x y C eq_refl Hx Hy (Hzs C Hc) Hxy HyC)).
    (* class types, nullable or not, and nullable unions: through the nullable ones *)
    all: subst.
    all: repeat match goal with H: in_fragment env ?t = true |- _ =>
        destruct (fragment_cases env t H) as [[? [? [? ->]]]|[? [? [? [-> _]]]]]; clear H end.
    all: repeat match goal with
         | H: assignable (Nullable _) (RootResolved _ _ _) |- _ => exfalso; exact (nullable_not_below_root env _ _ _ _ H)
         | H: assignable (RootResolved ?m ?c ?a) (Nullable ?y) |- _ => apply (below_nullable_root env m c a y) in H
         | H: assignable (Nullable ?x') (Nullable ?y) |- _ => apply (below_nullable_nullable env x' y) in H
         | |- assignable (RootResolved ?m ?c ?a) (Nullable ?y) => apply (below_nullable_root env m c a y)
         | |- assignable (Nullable ?x') (Nullable ?y) => apply (below_nullable_nullable env x' y)
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

Let assignable := Closed.assignable env.
Let never_fails := Closed.never_fails env.
Let answers := Closed.answers env.

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

Lemma kugfrag_no_vars: forall t, kugfrag env t = true -> no_vars t = true.
Proof.
    intros t H. destruct (kugfrag_cases env t H) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]]; [exact (gfrag_no_vars env t Hg)| |];
        cbn [no_vars]; apply forallb_forall; intros C Hc; exact (gfrag_no_vars env C (kept_union_component_gfrag env C (Hus C Hc))).
Qed.

Lemma kcomponents_no_vars: forall us, kugfrag env (Union us) = true -> forallb no_vars us = true.
Proof. intros us H. exact (kugfrag_no_vars (Union us) H). Qed.

Lemma kcomponent_gfrag: forall us C, kugfrag env (Union us) = true -> In C us -> gfrag env C = true.
Proof. intros us C H Hc. exact (kept_union_component_gfrag env C (proj2 (kugfrag_union env us H) C Hc)). Qed.

(* The types of the fragment as the targets of a union assignee, and as the assignees of a union target *)
Lemma kugfrag_takes_unions: forall t, kugfrag env t = true -> match t with Intersection _ => False | _ => True end -> takes_unions t.
Proof. intros t H Hs. pose proof (kugfrag_shape env t H). destruct t as [| | | | | | |]; try contradiction; exact I. Qed.

Lemma gfrag_searched_in_unions: forall t, gfrag env t = true -> match t with Intersection _ => False | _ => True end -> searched_in_unions t.
Proof. intros t H Hs. pose proof (gfrag_cases env t H) as Hc. destruct t as [| | | | | | |]; try exact I; try contradiction; simpl in H; discriminate H. Qed.

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

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the assignee: taken where each component is, an intersection target included         *)
(* ---------------------------------------------------------------------------------------------- *)

(* An intersection target takes each component of the union with each of its components; it takes the union
   with each of them (Rules.intersection_target_components, union_assignee_components) *)
Lemma ugfrag_union_components: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    assignable (Union us) y -> forall C, In C us -> assignable C y.
Proof.
    intros us y Hus Hy H C Hc. pose proof (union_components_no_vars us Hus) as Hvus. pose proof (ugfrag_no_vars y Hy) as Hvy.
    pose proof (gfrag_no_vars env C (component_gfrag us C Hus Hc)) as Hvc.
    destruct y as [| | | | | |ys|]; try exact (union_assignee_components env wf _ us Hvy Hvus (kugfrag_takes_unions _ (ugfrag_kugfrag env _ Hy) I) H C Hc).
    pose proof (gfrag_components_no_vars env ys Hy) as Hvys.
    apply (intersection_target_takes env wf ys C Hvys Hvc ltac:(pose proof (component_flat us C Hus Hc); destruct C as [| | | | | | |]; try contradiction; exact I)).
    intros Y Hin. pose proof (intersection_component_shape ys Y Hy Hin) as Hsh.
    apply (union_assignee_components env wf Y us (gfrag_no_vars env Y (intersection_component_gfrag ys Y Hy Hin)) Hvus
        ltac:(destruct Y as [| | | | | | |]; try contradiction; exact I)); [|exact Hc].
    exact (intersection_target_components env wf ys (Union us) Hvys Hvus I H Y Hin).
Qed.

Lemma ugfrag_union_taken: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    (forall C, In C us -> assignable C y) -> assignable (Union us) y.
Proof.
    intros us y Hus Hy H. pose proof (union_components_no_vars us Hus) as Hvus. pose proof (ugfrag_no_vars y Hy) as Hvy.
    destruct y as [| | | | | |ys|]; try exact (union_assignee_taken env wf _ us Hvy Hvus (kugfrag_takes_unions _ (ugfrag_kugfrag env _ Hy) I) H).
    pose proof (gfrag_components_no_vars env ys Hy) as Hvys.
    apply (intersection_target_takes env wf ys (Union us) Hvys Hvus I). intros Y Hin. pose proof (intersection_component_shape ys Y Hy Hin) as Hsh.
    apply (union_assignee_taken env wf Y us (gfrag_no_vars env Y (intersection_component_gfrag ys Y Hy Hin)) Hvus
        ltac:(destruct Y as [| | | | | | |]; try contradiction; exact I)).
    intros C Hc. pose proof (component_flat us C Hus Hc) as Hfc.
    exact (intersection_target_components env wf ys C Hvys (gfrag_no_vars env C (component_gfrag us C Hus Hc))
        ltac:(destruct C as [| | | | | | |]; try contradiction; exact I) (H C Hc) Y Hin).
Qed.

(* A union is below a type exactly where each of its components is *)
Theorem union_below_iff_in_generic_code: forall us y, ugfrag env (Union us) = true -> ugfrag env y = true ->
    assignable (Union us) y <-> forall C, In C us -> assignable C y.
Proof. intros us y Hus Hy. split; [exact (ugfrag_union_components us y Hus Hy)|exact (ugfrag_union_taken us y Hus Hy)]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A union as the target                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* Only a nullable type takes a possibly null value, and takes what it wraps *)
Theorem nullable_assignee_target: forall x y, no_vars x = true -> kugfrag env y = true -> assignable (Nullable x) y ->
    exists y', y = Nullable y' /\ assignable x y'.
Proof.
    intros x y Hx Hy H.
    destruct (kugfrag_cases env y Hy) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - destruct H as [n H]. destruct (gfrag_cases env y Hg) as [[m [c [args ->]]]|[[y' [-> _]]|[[gm [nn [p [vs [-> _]]]]]|[cs ->]]]];
          try (exfalso; exact (nullable_rejected env n _ x Hg I H)).
      exists y'. split; [reflexivity|]. destruct n as [|n]; [discriminate H|]. exists n. exact H.
    - exfalso. destruct (union_target_component env wf us (Nullable x) (kcomponents_no_vars us Hy) Hx I H) as [C [Hc [n HC]]].
      exact (nullable_rejected env n C x (kept_union_component_gfrag env C (Hus C Hc)) (kept_union_component_flat env C (Hus C Hc)) HC).
    - exists (Union us). split; [reflexivity|]. exact (proj1 (below_nullable_nullable env x (Union us)) H).
Qed.

(* An intersection is taken by a union by a component of it that is below one of the components of the union, or as
   a whole: `(A | B) & C` is below `A | B` by its component `A | B` (the frontend distributes, so the component there
   is `A & C`, below `A`) *)
Theorem union_target_intersection: forall us cs, kugfrag env (Union us) = true -> gfrag env (Intersection cs) = true ->
    assignable (Intersection cs) (Union us) ->
    (exists y, In y us /\ assignable (Intersection cs) y) \/ (exists C y, In C cs /\ In y us /\ assignable C y).
Proof.
    intros us cs Hus Hcs H. pose proof (kcomponents_no_vars us Hus) as Hvus.
    destruct (intersection_below_union env wf us cs Hvus (gfrag_components_no_vars env cs Hcs) H) as [[C [Hc HCu]]|Hwhole]; [right|left; exact Hwhole].
    pose proof (intersection_component_shape cs C Hcs Hc) as Hsh. pose proof (gfrag_no_vars env C (intersection_component_gfrag cs C Hcs Hc)) as Hvc.
    destruct C as [m c args|x|g|me msg|v o x|g|cs'|us']; try contradiction.
    - destruct (union_target_component env wf us (RootResolved m c args) Hvus Hvc I HCu) as [y [Hy Hxy]]. exists (RootResolved m c args), y. auto.
    - exfalso. destruct (nullable_assignee_target x (Union us) Hvc Hus HCu) as [y' [Eq _]]. discriminate Eq.
    - destruct (union_target_component env wf us (Generic g) Hvus Hvc I HCu) as [y [Hy Hxy]]. exists (Generic g), y. auto.
Qed.

(* A union never rejects a type of values that one of its components never rejects *)
Lemma union_never_fails_flat: forall us x C, forallb no_vars us = true -> no_vars x = true -> In C us -> flat x ->
    never_fails C x -> never_fails (Union us) x.
Proof.
    intros us x C Hus Hx Hc Hf H. destruct x as [| | | | | |cs|]; try contradiction;
        try exact (union_target_never_fails env wf us _ C Hus Hx I Hc H).
    exact (union_component_intersection_never_fails env wf us cs C Hus Hx Hc H).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Nullable types and intersections of the fragment                                                *)
(* ---------------------------------------------------------------------------------------------- *)

(* An intersection that takes a possibly null value keeps the nullability of its components *)
Lemma nullable_below_intersection: forall y' zs, assignable (Nullable y') (Intersection zs) -> is_nullable env (Intersection zs) = true.
Proof.
    intros y' zs [n H]. destruct n as [|n]; [discriminate H|]. destruct (is_nullable env (Intersection zs)) eqn:E; [reflexivity|].
    unfold is_assignable_to, empty_unification in H. rewrite (step_inter_nullable env n zs y' [] E) in H. discriminate H.
Qed.

(* What an intersection target takes, each of its components takes: of the fragment, the shape of the assignee
   is as the intersection takes it *)
Lemma intersection_target_shape: forall zs y, kugfrag env y = true -> assignable y (Intersection zs) -> inter_shape env zs y.
Proof.
    intros zs y Hy H. pose proof (kugfrag_shape env y Hy) as Hs. destruct y as [|y'| | | | | |]; try contradiction; try exact I.
    cbn [inter_shape]. exact (nullable_below_intersection y' zs H).
Qed.

Lemma ugfrag_intersection_components: forall zs y, gfrag env (Intersection zs) = true -> kugfrag env y = true ->
    assignable y (Intersection zs) -> forall C, In C zs -> assignable y C.
Proof.
    intros zs y Hzs Hy H.
    exact (intersection_target_components env wf zs y (gfrag_components_no_vars env zs Hzs) (kugfrag_no_vars y Hy) (intersection_target_shape zs y Hy H) H).
Qed.

Lemma nullable_intersection_target_components: forall zs y, gfrag env (Nullable (Intersection zs)) = true -> ugfrag env y = true ->
    assignable y (Nullable (Intersection zs)) -> forall C, In C zs -> assignable y (Nullable C).
Proof.
    intros zs y Hz Hy H C Hc. pose proof (nullable_intersection_gfrag zs Hz) as Hzs. pose proof (nullable_component_gfrag zs C Hz Hc) as HC.
    destruct (ugfrag_cases env y Hy) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - apply (below_nullable env y C Hg).
      exact (ugfrag_intersection_components zs _ Hzs (gfrag_kugfrag env _ (gfrag_without_null env wf declared declared_wf y Hg))
          (proj1 (below_nullable env y (Intersection zs) Hg) H) C Hc).
    - apply (ugfrag_union_taken us (Nullable C) Hy (gfrag_ugfrag env _ HC)). intros D Hd.
      pose proof (component_gfrag us D Hy Hd) as HD. apply (below_nullable env D C HD).
      apply (ugfrag_intersection_components zs _ Hzs (gfrag_kugfrag env _ (gfrag_without_null env wf declared declared_wf D HD))); [|exact Hc].
      apply (below_nullable env D (Intersection zs) HD). exact (ugfrag_union_components us _ Hy (gfrag_ugfrag env _ Hz) H D Hd).
    - apply (below_nullable_nullable env). apply (ugfrag_intersection_components zs (Union us) Hzs (ugfrag_kugfrag env _ Hy)); [|exact Hc].
      apply (below_nullable_nullable env). exact H.
Qed.

Lemma nullable_intersection_target_never_fails: forall zs x, gfrag env (Intersection zs) = true -> gfrag env x = true ->
    (forall C, In C zs -> never_fails (Nullable C) x) -> never_fails (Nullable (Intersection zs)) x.
Proof.
    intros zs x Hzs Hx H. apply (nullable_target_never_fails env _ x Hx).
    pose proof (gfrag_without_null env wf declared declared_wf x Hx) as Hw. pose proof (without_null_shape env x) as Hs.
    apply (intersection_target_never_fails env wf zs _ (gfrag_components_no_vars env zs Hzs) (gfrag_no_vars env _ Hw)).
    - remember (without_null env x) as w eqn:Ew. destruct w as [| | | | | | |]; try exact I; try contradiction; simpl in Hw; discriminate Hw.
    - intros C Hc. exact (nullable_target_strip env C x Hx (H C Hc)).
Qed.

(* A target of the fragment that is no intersection never rejects an intersection with a component it never rejects *)
Lemma intersection_assignee_never_fails: forall z cs C, ugfrag env z = true ->
    match z with Intersection _ | Nullable (Intersection _) => False | _ => True end ->
    gfrag env (Intersection cs) = true -> In C cs -> never_fails z C -> never_fails z (Intersection cs).
Proof.
    intros z cs C Hz Hsz Hcs Hc H. pose proof (intersection_component_gfrag cs C Hcs Hc) as HC.
    pose proof (gfrag_components_no_vars env cs Hcs) as Hvcs. pose proof (ugfrag_no_vars z Hz) as Hvz.
    pose proof (gfrag_without_null env wf declared declared_wf _ Hcs) as Hw. rewrite (without_null_intersection cs Hcs) in Hw.
    pose proof (gfrag_components_no_vars env _ Hw) as Hvw.
    destruct (ugfrag_cases env z Hz) as [Hg|[[us [-> [_ Hus]]]|[us [-> [_ Hus]]]]].
    - destruct (gfrag_cases env z Hg) as [[m [c [args ->]]]|[[z' [-> [Hnz Hgz]]]|[[gm [nn [p [vs [-> _]]]]]|[zs ->]]]]; try (exfalso; exact Hsz).
      + exact (flat_target_intersection_never_fails env wf (RootResolved m c args) cs C Hvz Hvcs I Hc H).
      + (* a nullable type: what it wraps never rejects the component without null, so the intersection without null *)
        apply (nullable_target_never_fails env z' _ Hcs). rewrite (without_null_intersection cs Hcs).
        pose proof (nullable_target_strip env z' C HC H) as H'.
        assert (Hin: In (without_null env C) (map (without_null env) cs)) by (apply in_map, Hc).
        pose proof (gfrag_no_vars env z' Hgz) as Hvz'.
        destruct (gfrag_cases env z' Hgz) as [[m [c [args ->]]]|[[z'' [-> [Hnz' _]]]|[[gm [nn [p [vs [-> _]]]]]|[zs ->]]]].
        * exact (flat_target_intersection_never_fails env wf (RootResolved m c args) _ _ Hvz' Hvw I Hin H').
        * exfalso. cbn [non_null is_component] in Hnz. discriminate Hnz.
        * exact (flat_target_intersection_never_fails env wf (Generic (mkGenericRef gm nn p vs)) _ _ Hvz' Hvw I Hin H').
        * exfalso. exact Hsz.
      + exact (flat_target_intersection_never_fails env wf (Generic (mkGenericRef gm nn p vs)) cs C Hvz Hvcs I Hc H).
    - exact (union_target_intersection_never_fails env wf us cs C Hvz Hvcs Hc H).
    - apply (nullable_target_never_fails env _ _ Hcs). rewrite (without_null_intersection cs Hcs).
      exact (union_target_intersection_never_fails env wf us _ _ Hvz Hvw (in_map _ cs C Hc) (nullable_target_strip env _ C HC H)).
Qed.

(* An intersection is below a class type or a reference, nullable or not, by one of its components *)
Lemma intersection_assignee_below_flat: forall ys z, gfrag env (Intersection ys) = true -> gfrag env z = true ->
    match z with RootResolved _ _ _ | Generic _ | Nullable (RootResolved _ _ _) | Nullable (Generic _) => True | _ => False end ->
    assignable (Intersection ys) z -> exists C, In C ys /\ assignable C z.
Proof.
    intros ys z Hys Hz Hs H. pose proof (gfrag_components_no_vars env ys Hys) as Hvys. pose proof (gfrag_no_vars env _ Hz) as Hvz.
    destruct z as [m c args|z'|g|me msg|v o z'|g|zs|us]; try contradiction;
        try exact (intersection_assignee_component env wf _ ys Hvz Hvys I H).
    (* nullable: what it wraps takes the intersection without null, by one of its components *)
    pose proof (gfrag_nullable_inner env z' Hz) as Hgz. apply (below_nullable env _ z' Hys) in H. rewrite (without_null_intersection ys Hys) in H.
    pose proof (gfrag_without_null env wf declared declared_wf _ Hys) as Hw. rewrite (without_null_intersection ys Hys) in Hw.
    destruct (intersection_assignee_component env wf z' _ (gfrag_no_vars env z' Hgz) (gfrag_components_no_vars env _ Hw)
        ltac:(destruct z' as [| | | | | | |]; try (exfalso; exact Hs); exact I) H) as [C' [Hc' HC']].
    apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. exists C. split; [exact Hc|].
    apply (below_nullable env C z' (intersection_component_gfrag ys C Hys Hc)). exact HC'.
Qed.

(* ... and below a nullable union likewise, the union taking the intersection without null *)
Lemma intersection_assignee_below_nullable_union: forall ys zs, gfrag env (Intersection ys) = true -> forallb no_vars zs = true ->
    assignable (Intersection ys) (Nullable (Union zs)) ->
    (exists C, In C ys /\ assignable C (Nullable (Union zs))) \/ (exists y, In y zs /\ assignable (Intersection ys) (Nullable y)).
Proof.
    intros ys zs Hys Hzs H. apply (below_nullable env _ _ Hys) in H. rewrite (without_null_intersection ys Hys) in H.
    pose proof (gfrag_without_null env wf declared declared_wf _ Hys) as Hw. rewrite (without_null_intersection ys Hys) in Hw.
    destruct (intersection_below_union env wf zs _ Hzs (gfrag_components_no_vars env _ Hw) H) as [[C' [Hc' HC']]|[y [Hy Hu]]].
    - left. apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. exists C. split; [exact Hc|].
      apply (below_nullable env C _ (intersection_component_gfrag ys C Hys Hc)). exact HC'.
    - right. exists y. split; [exact Hy|]. apply (below_nullable env _ y Hys). rewrite (without_null_intersection ys Hys). exact Hu.
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
    pose proof (ugfrag_kugfrag env x Hx) as Kx. pose proof (ugfrag_kugfrag env y Hy) as Ky. pose proof (ugfrag_kugfrag env z Hz) as Kz.
    (* z an intersection: each of its components takes y, and never rejects x *)
    assert (HZI: forall zs, z = Intersection zs -> never_fails z x).
    { intros zs Ez. subst z.
      apply (intersection_target_never_fails env wf zs x (gfrag_components_no_vars env zs Hz) Hvx).
      - pose proof (ugfrag_shape env x Hx) as Hs. destruct x as [|x'| | | | | |]; try contradiction; try exact I.
        cbn [inter_shape]. destruct (nullable_assignee_target x' y Hvx Ky Hxy) as [y' [Ey Hy']]. subst y.
        exact (nullable_below_intersection y' zs Hyz).
      - intros C Hc. pose proof (esize_in zs C Hc). pose proof (intersection_component_gfrag zs C Hz Hc) as HC.
        exact (IH (esize x + esize y + esize C) ltac:(cbn [esize]; lia) x y C eq_refl Hx Hy (gfrag_ugfrag env C HC) Hxy
            (ugfrag_intersection_components zs y Hz Ky Hyz C Hc)). }
    (* z a nullable intersection: each of its components, made nullable, takes y *)
    assert (HZN: forall zs, z = Nullable (Intersection zs) -> never_fails z x).
    { intros zs Ez. subst z. pose proof (nullable_intersection_gfrag zs Hz) as Hzs.
      assert (HIH: forall C, In C zs -> never_fails (Nullable C) x).
      { intros C Hc. pose proof (esize_in zs C Hc). pose proof (nullable_component_gfrag zs C Hz Hc) as HC.
        exact (IH (esize x + esize y + esize (Nullable C)) ltac:(cbn [esize]; lia) x y (Nullable C) eq_refl Hx Hy (gfrag_ugfrag env _ HC) Hxy
            (nullable_intersection_target_components zs y Hz Hy Hyz C Hc)). }
      destruct (ugfrag_cases env x Hx) as [Gx|[[xs [Ex [_ Hxs]]]|[xs [Ex [_ Hxs]]]]].
      - exact (nullable_intersection_target_never_fails zs x Hzs Gx HIH).
      - subst x. apply (union_assignee_never_fails env wf (Nullable (Intersection zs)) xs Hvz (union_components_no_vars xs Hx) I).
        intros C Hc. pose proof (esize_in xs C Hc).
        exact (IH (esize C + esize y + esize (Nullable (Intersection zs))) ltac:(cbn [esize]; lia) C y _ eq_refl
            (gfrag_ugfrag env C (component_gfrag xs C Hx Hc)) Hy Hz (ugfrag_union_components xs y Hx Hy Hxy C Hc) Hyz).
      - subst x. destruct (nullable_assignee_target (Union xs) y Hvx Ky Hxy) as [y' [Ey Hy']]. subst y.
        intros n E. destruct n as [|n]; [discriminate E|].
        exact (IH (esize (Union xs) + esize y' + esize (Intersection zs)) ltac:(cbn [esize]; lia) (Union xs) y' (Intersection zs) eq_refl
            Hx (ugfrag_nullable env y' Hy) (gfrag_ugfrag env _ Hzs) Hy' (proj1 (below_nullable_nullable env y' (Intersection zs)) Hyz) n E). }
    (* the rest: z is a class type, a reference, a union, or one of them made nullable *)
    assert (Hflat: match z with Intersection _ | Nullable (Intersection _) => False | _ => True end -> never_fails z x).
    { intros Hsz.
      destruct (ugfrag_cases env x Hx) as [Gx|[[xs [Ex [_ Hxs]]]|[xs [Ex [_ Hxs]]]]].
      2: { (* x a union: each component is below y, and never rejected by z *) subst x.
           apply (union_assignee_never_fails env wf z xs Hvz (union_components_no_vars xs Hx)).
           - pose proof (ugfrag_shape env z Hz) as Hs. destruct z as [| | | | | | |]; try contradiction; exact I.
           - intros C Hc. pose proof (esize_in xs C Hc).
             exact (IH (esize C + esize y + esize z) ltac:(cbn [esize]; lia) C y z eq_refl (gfrag_ugfrag env C (component_gfrag xs C Hx Hc)) Hy Hz
                 (ugfrag_union_components xs y Hx Hy Hxy C Hc) Hyz). }
      2: { (* x a nullable union: y and z are nullable, and the union is below what they wrap *) subst x.
           destruct (nullable_assignee_target (Union xs) y Hvx Ky Hxy) as [y' [Ey Hy']]. subst y.
           destruct (nullable_assignee_target y' z (ugfrag_no_vars _ (ugfrag_nullable env y' Hy)) Kz Hyz) as [z' [Ez Hz']]. subst z.
           intros n E. destruct n as [|n]; [discriminate E|].
           exact (IH (esize (Union xs) + esize y' + esize z') ltac:(cbn [esize]; lia) (Union xs) y' z' eq_refl Hx (ugfrag_nullable env y' Hy)
               (ugfrag_nullable env z' Hz) Hy' Hz' n E). }
      (* x of gfrag *)
      destruct (ugfrag_cases env y Hy) as [Gy|[[ys [Ey [_ Hys]]]|[ys [Ey [_ Hys]]]]].
      2: { (* y a union: x is below one of its components, or a component of x is; each is below z *) subst y.
           assert (Hcomp: forall C, In C ys -> assignable C z) by exact (ugfrag_union_components ys z Hy Hz Hyz).
           assert (Hvia: forall x', ugfrag env x' = true -> esize x' <= esize x -> (exists C, In C ys /\ assignable x' C) -> never_fails z x').
           { intros x' Hx' Hsize [C [Hc HC]]. pose proof (esize_in ys C Hc).
             exact (IH (esize x' + esize C + esize z) ltac:(cbn [esize]; lia) x' C z eq_refl Hx' (gfrag_ugfrag env C (component_gfrag ys C Hy Hc)) Hz HC (Hcomp C Hc)). }
           pose proof (ugfrag_shape env x Hx) as Hs. pose proof (union_components_no_vars ys Hy) as Hvys.
           destruct x as [m c args|x'|g|me msg|v o x'|g|cs|us]; try contradiction.
           - exact (Hvia _ Hx (le_n _) (union_target_component env wf ys (RootResolved m c args) Hvys Hvx I Hxy)).
           - exfalso. destruct (nullable_assignee_target x' (Union ys) Hvx Ky Hxy) as [y' [Eyn _]]. discriminate Eyn.
           - exact (Hvia _ Hx (le_n _) (union_target_component env wf ys (Generic g) Hvys Hvx I Hxy)).
           - destruct (union_target_intersection ys cs Ky Gx Hxy) as [[y' [Hy' Hu]]|[C [y' [Hc [Hy' HC]]]]].
             + exact (Hvia _ Hx (le_n _) (ex_intro _ y' (conj Hy' Hu))).
             + pose proof (esize_in cs C Hc). pose proof (esize_in ys y' Hy'). pose proof (intersection_component_gfrag cs C Gx Hc) as HC'.
               apply (intersection_assignee_never_fails z cs C Hz Hsz Gx Hc).
               exact (IH (esize C + esize y' + esize z) ltac:(cbn [esize]; lia) C y' z eq_refl (gfrag_ugfrag env C HC')
                   (gfrag_ugfrag env y' (component_gfrag ys y' Hy Hy')) Hz HC (Hcomp y' Hy')).
           - simpl in Gx. discriminate Gx. }
      2: { (* y a nullable union: z is nullable, and x without null is below a component of y, or a component of x is *) subst y.
           destruct (nullable_assignee_target (Union ys) z Hvy Kz Hyz) as [z' [Ez Hz']]. subst z.
           pose proof (ugfrag_nullable env z' Hz) as Hz''. pose proof (ugfrag_kugfrag env z' Hz'') as Kz'.
           pose proof (union_components_no_vars ys Hy) as Hvys.
           assert (Hcomp: forall C, In C ys -> assignable C z') by exact (ugfrag_union_components ys z' Hy Hz'' Hz').
           assert (Hvia: forall x', gfrag env x' = true -> esize x' <= esize x -> (exists C, In C ys /\ assignable (without_null env x') C) ->
               never_fails (Nullable z') x').
           { intros x' Hx' Hsize [C [Hc HC]]. pose proof (esize_in ys C Hc).
             exact (IH (esize x' + esize (Nullable C) + esize (Nullable z')) ltac:(cbn [esize]; lia) x' (Nullable C) (Nullable z') eq_refl
                 (gfrag_ugfrag env x' Hx') (gfrag_ugfrag env _ (component_nullable_gfrag ys C Hy Hc)) Hz (proj2 (below_nullable env x' C Hx') HC)
                 (proj2 (below_nullable_nullable env C z') (Hcomp C Hc))). }
           pose proof (proj1 (below_nullable env x (Union ys) Gx) Hxy) as Hwx.
           pose proof (gfrag_no_vars env _ (gfrag_without_null env wf declared declared_wf x Gx)) as Hvw.
           destruct (gfrag_cases env x Gx) as [[m [c [args Ex]]]|[[x' [Ex [Hnn Gx']]]|[[gm [nn [p [vs [Ex _]]]]]|[cs Ex]]]]; subst x.
           - rewrite (without_null_unchanged env (RootResolved m c args) eq_refl) in Hwx, Hvw. apply (Hvia _ Gx (le_n _)).
             rewrite (without_null_unchanged env (RootResolved m c args) eq_refl). exact (union_target_component env wf ys (RootResolved m c args) Hvys Hvw I Hwx).
           - (* a nullable type: what it wraps is below the union, as a whole or by a component *)
             assert (Ew: without_null env (Nullable x') = x') by (cbn [without_null]; exact (without_null_unchanged env x' (non_null_not_nullable env x' Hnn))).
             rewrite Ew in Hwx, Hvw. pose proof (ugfrag_shape env _ (gfrag_ugfrag env _ Gx')) as Hs.
             destruct x' as [m c args|x''|g|me msg|v o x''|g|cs|us]; try contradiction.
             + apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (union_target_component env wf ys (RootResolved m c args) Hvys Hvw I Hwx).
             + exfalso. cbn [non_null is_component] in Hnn. discriminate Hnn.
             + apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (union_target_component env wf ys (Generic g) Hvys Hvw I Hwx).
             + destruct (union_target_intersection ys cs Ky Gx' Hwx) as [[y' [Hy' Hu]]|[C [y' [Hc [Hy' HC]]]]].
               * apply (Hvia _ Gx (le_n _)). rewrite Ew. exact (ex_intro _ y' (conj Hy' Hu)).
               * (* a component of the intersection is below a component of the union, which is below z' *)
                 intros n E. destruct n as [|n]; [discriminate E|].
                 assert (Hsz': match z' with Intersection _ | Nullable (Intersection _) => False | _ => True end).
                 { destruct z' as [| [| | | | | | |] | | | | | |]; try exact I; try exact Hsz; simpl in Hz; discriminate Hz. }
                 refine (intersection_assignee_never_fails z' cs C Hz'' Hsz' Gx' Hc _ n E).
                 pose proof (esize_in cs C Hc). pose proof (esize_in ys y' Hy'). pose proof (intersection_component_gfrag cs C Gx' Hc) as HC'.
                 exact (IH (esize C + esize y' + esize z') ltac:(cbn [esize]; lia) C y' z' eq_refl (gfrag_ugfrag env C HC')
                     (gfrag_ugfrag env y' (component_gfrag ys y' Hy Hy')) Hz'' HC (Hcomp y' Hy')).
             + simpl in Gx'. discriminate Gx'.
           - apply (Hvia _ Gx (le_n _)). exact (union_target_component env wf ys (without_null env (Generic (mkGenericRef gm nn p vs))) Hvys Hvw I Hwx).
           - (* an intersection: without null, it is below the union as a whole, or by a component *)
             rewrite (without_null_intersection cs Gx) in Hwx.
             pose proof (gfrag_without_null env wf declared declared_wf _ Gx) as Hw. rewrite (without_null_intersection cs Gx) in Hw.
             destruct (union_target_intersection ys _ Ky Hw Hwx) as [[y' [Hy' Hu]]|[C' [y' [Hc' [Hy' HC']]]]].
             + apply (Hvia _ Gx (le_n _)). exists y'. split; [exact Hy'|]. rewrite (without_null_intersection cs Gx). exact Hu.
             + apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. pose proof (esize_in cs C Hc).
               apply (intersection_assignee_never_fails (Nullable z') cs C Hz Hsz Gx Hc).
               apply (Hvia C (intersection_component_gfrag cs C Gx Hc) ltac:(cbn [esize]; lia)). exists y'. exact (conj Hy' HC'). }
      (* x and y of gfrag *)
      destruct (ugfrag_cases env z Hz) as [Gz|[[zs [Ez [_ Hzs]]]|[zs [Ez [_ Hzs]]]]].
      - (* all three of the fragment of type parameters and intersections: Generics.v *)
        destruct Hxy as [n1 H1]. destruct Hyz as [n2 H2].
        exact (transitivity_never_fails env wf declared declared_wf n1 n2 x y z Gx Gy Gz I I I H1 H2).
      - (* z a union: y, or a component of it, is below a component of z *) subst z. pose proof (union_components_no_vars zs Hz) as Hvzs.
        assert (Hfx: flat x).
        { pose proof (ugfrag_shape env x Hx) as Hs. destruct x as [|x'| | | | | |]; try contradiction; try exact I.
          - exfalso. destruct (nullable_assignee_target x' y Hvx Ky Hxy) as [y' [Eyn _]]. subst y.
            destruct (nullable_assignee_target y' (Union zs) (ugfrag_no_vars _ (ugfrag_nullable env y' Hy)) Kz Hyz) as [z' [Ezn _]]. discriminate Ezn.
          - simpl in Gx. discriminate Gx. }
        assert (Hvia: forall y', ugfrag env y' = true -> esize y' <= esize y -> assignable x y' -> (exists C, In C zs /\ assignable y' C) ->
            never_fails (Union zs) x).
        { intros y' Hy' Hsize Hxy' [C [Hc HC]]. pose proof (esize_in zs C Hc).
          apply (union_never_fails_flat zs x C Hvzs Hvx Hc Hfx).
          exact (IH (esize x + esize y' + esize C) ltac:(cbn [esize]; lia) x y' C eq_refl Hx Hy' (gfrag_ugfrag env C (component_gfrag zs C Hz Hc)) Hxy' HC). }
        destruct (gfrag_cases env y Gy) as [[m [c [args Ey]]]|[[y' [Ey [Hnn Gy']]]|[[gm [nn [p [vs [Ey _]]]]]|[ys Ey]]]]; subst y.
        + exact (Hvia _ Hy (le_n _) Hxy (union_target_component env wf zs (RootResolved m c args) Hvzs Hvy I Hyz)).
        + exfalso. destruct (nullable_assignee_target y' (Union zs) Hvy Kz Hyz) as [z' [Ezn _]]. discriminate Ezn.
        + exact (Hvia _ Hy (le_n _) Hxy (union_target_component env wf zs (Generic (mkGenericRef gm nn p vs)) Hvzs Hvy I Hyz)).
        + destruct (intersection_below_union env wf zs ys Hvzs (gfrag_components_no_vars env ys Gy) Hyz) as [[C [Hc HC]]|[y' [Hy' Hu]]].
          * pose proof (esize_in ys C Hc). pose proof (intersection_component_gfrag ys C Gy Hc) as HC'.
            exact (IH (esize x + esize C + esize (Union zs)) ltac:(cbn [esize]; lia) x C (Union zs) eq_refl Hx (gfrag_ugfrag env C HC') Hz
                (ugfrag_intersection_components ys x Gy Kx Hxy C Hc) HC).
          * exact (Hvia _ Hy (le_n _) Hxy (ex_intro _ y' (conj Hy' Hu))).
      - (* z a nullable union: y without null is below a component of z, as a whole or by a component *) subst z.
        pose proof (union_components_no_vars zs Hz) as Hvzs.
        apply (nullable_target_never_fails env (Union zs) x Gx).
        pose proof (gfrag_without_null env wf declared declared_wf x Gx) as Hgw. pose proof (gfrag_no_vars env _ Hgw) as Hvw.
        assert (Hfw: flat (without_null env x)).
        { pose proof (without_null_shape env x) as Hs.
          remember (without_null env x) as w eqn:Ew. destruct w as [| | | | | | |]; try exact I; try contradiction; simpl in Hgw; discriminate Hgw. }
        assert (Hvia: forall y', gfrag env y' = true -> esize y' <= esize y -> assignable x y' -> (exists C, In C zs /\ assignable (without_null env y') C) ->
            never_fails (Union zs) (without_null env x)).
        { intros y' Hy' Hsize Hxy' [C [Hc HC]]. pose proof (esize_in zs C Hc).
          apply (union_never_fails_flat zs _ C Hvzs Hvw Hc Hfw).
          apply (nullable_target_strip env C x Gx).
          exact (IH (esize x + esize y' + esize (Nullable C)) ltac:(cbn [esize]; lia) x y' (Nullable C) eq_refl Hx (gfrag_ugfrag env y' Hy')
              (gfrag_ugfrag env _ (component_nullable_gfrag zs C Hz Hc)) Hxy' (proj2 (below_nullable env y' C Hy') HC)). }
        pose proof (proj1 (below_nullable env y (Union zs) Gy) Hyz) as Hwy.
        pose proof (gfrag_no_vars env _ (gfrag_without_null env wf declared declared_wf y Gy)) as Hvwy.
        destruct (gfrag_cases env y Gy) as [[m [c [args Ey]]]|[[y' [Ey [Hnn Gy']]]|[[gm [nn [p [vs [Ey _]]]]]|[ys Ey]]]]; subst y.
        + rewrite (without_null_unchanged env (RootResolved m c args) eq_refl) in Hwy, Hvwy. apply (Hvia _ Gy (le_n _) Hxy).
          rewrite (without_null_unchanged env (RootResolved m c args) eq_refl). exact (union_target_component env wf zs (RootResolved m c args) Hvzs Hvwy I Hwy).
        + (* a nullable type: what it wraps is below the union *)
          assert (Ew: without_null env (Nullable y') = y') by (cbn [without_null]; exact (without_null_unchanged env y' (non_null_not_nullable env y' Hnn))).
          rewrite Ew in Hwy, Hvwy. pose proof (ugfrag_shape env _ (gfrag_ugfrag env _ Gy')) as Hs.
          destruct y' as [m c args|y''|g|me msg|v o y''|g|ys|us]; try contradiction.
          * apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (union_target_component env wf zs (RootResolved m c args) Hvzs Hvwy I Hwy).
          * exfalso. cbn [non_null is_component] in Hnn. discriminate Hnn.
          * apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (union_target_component env wf zs (Generic g) Hvzs Hvwy I Hwy).
          * destruct (intersection_below_union env wf zs ys Hvzs (gfrag_components_no_vars env ys Gy') Hwy) as [[C [Hc HC]]|[y' [Hy' Hu]]].
            { (* x is below the component made nullable, which is below z *)
              pose proof (esize_in ys C Hc). pose proof (nullable_component_gfrag ys C Gy Hc) as HC'.
              apply (nullable_target_strip env (Union zs) x Gx).
              exact (IH (esize x + esize (Nullable C) + esize (Nullable (Union zs))) ltac:(cbn [esize]; lia) x (Nullable C) (Nullable (Union zs)) eq_refl
                  Hx (gfrag_ugfrag env _ HC') Hz (nullable_intersection_target_components ys x Gy Hx Hxy C Hc)
                  (proj2 (below_nullable_nullable env C (Union zs)) HC)). }
            { apply (Hvia _ Gy (le_n _) Hxy). rewrite Ew. exact (ex_intro _ y' (conj Hy' Hu)). }
          * simpl in Gy'. discriminate Gy'.
        + apply (Hvia _ Gy (le_n _) Hxy). exact (union_target_component env wf zs (without_null env (Generic (mkGenericRef gm nn p vs))) Hvzs Hvwy I Hwy).
        + (* an intersection: a component of it is below z, or a component of z takes it without null *)
          rewrite (without_null_intersection ys Gy) in Hwy, Hvwy.
          destruct (intersection_below_union env wf zs _ Hvzs Hvwy Hwy) as [[C' [Hc' HC']]|[y' [Hy' Hu]]].
          * apply in_map_iff in Hc'. destruct Hc' as [C [<- Hc]]. pose proof (esize_in ys C Hc). pose proof (intersection_component_gfrag ys C Gy Hc) as HC.
            apply (nullable_target_strip env (Union zs) x Gx).
            exact (IH (esize x + esize C + esize (Nullable (Union zs))) ltac:(cbn [esize]; lia) x C (Nullable (Union zs)) eq_refl Hx (gfrag_ugfrag env C HC) Hz
                (ugfrag_intersection_components ys x Gy Kx Hxy C Hc) (proj2 (below_nullable env C (Union zs) HC) HC')).
          * apply (Hvia _ Gy (le_n _) Hxy). exists y'. split; [exact Hy'|]. rewrite (without_null_intersection ys Gy). exact Hu. }
    pose proof (ugfrag_shape env z Hz) as Hsz.
    destruct z as [mz cz zargs|z'|gz|me msg|v o z'|g|zs|zs]; try contradiction; try (apply Hflat; exact I); [|exact (HZI zs eq_refl)].
    destruct z' as [m c args|z''|g|me msg|v o z''|g|zs|zs]; try (apply Hflat; exact I). exact (HZN zs eq_refl).
Qed.

(* As Generics.transitivity_never_fails states it *)
Theorem transitivity_never_fails_with_unions: forall n1 n2 x y z,
    ugfrag env x = true -> ugfrag env y = true -> ugfrag env z = true ->
    refs_wf env declared x -> refs_wf env declared y -> refs_wf env declared z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    forall n3, is_assignable_to env n3 x z <> Some false.
Proof.
    intros n1 n2 x y z Hx Hy Hz _ _ _ H1 H2.
    exact (ugfrag_transitive_never_fails x y z Hx Hy Hz (ex_intro _ n1 H1) (ex_intro _ n2 H2)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Termination, and transitivity as usual                                                          *)
(* ---------------------------------------------------------------------------------------------- *)

(* Unify terminates on the types of the fragment of type parameters and intersections, in the environment at hand
   (Conjectures.unify_terminates_on): the premise of the theorems that an assignment is accepted *)
Hypothesis terminates: unify_terminates_on env declared.

Lemma gfrag_answers: forall t a, gfrag env t = true -> gfrag env a = true -> answers t a.
Proof.
    intros t a Ht Ha. destruct (terminates wf declared_wf t a [] Ht Ha I I) as [n H]. exists n.
    unfold is_assignable_to, empty_unification. destruct (unify env n t a (Ongoing [])); [discriminate|exfalso; exact (H eq_refl)].
Qed.

(* Then unify terminates on the fragment with unions, too: the components are tried one by one *)
Theorem kugfrag_terminates: forall t a, kugfrag env t = true -> kugfrag env a = true -> answers t a.
Proof.
    intros t a. remember (esize t + esize a) as k eqn:Hk. revert t a Hk. induction k as [k IH] using lt_wf_ind. intros t a -> Ht Ha.
    pose proof (kugfrag_no_vars t Ht) as Hvt. pose proof (kugfrag_no_vars a Ha) as Hva.
    (* a union assignee, to a target that is no intersection: each component *)
    assert (Hflip: forall us, kugfrag env (Union us) = true -> esize (Union us) <= esize a -> takes_unions t -> answers t (Union us)).
    { intros us Hus Hsz Hst. apply (union_assignee_answers env wf t us Hvt (kcomponents_no_vars us Hus) Hst).
      intros C Hc. pose proof (esize_in us C Hc).
      exact (IH (esize t + esize C) ltac:(cbn [esize] in Hsz; lia) t C eq_refl Ht (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc))). }
    (* a union target, and an assignee that is a type of values: the first component that takes it *)
    assert (Hsearch: forall us, kugfrag env (Union us) = true -> esize (Union us) <= esize t -> searched_in_unions a -> answers (Union us) a).
    { intros us Hus Hsz Hsa. apply (union_target_answers env wf us a (kcomponents_no_vars us Hus) Hva Hsa).
      intros C Hc. pose proof (esize_in us C Hc).
      exact (IH (esize C + esize a) ltac:(cbn [esize] in Hsz; lia) C a eq_refl (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc)) Ha). }
    (* ... and an intersection assignee: its components against the union, then the union's against it *)
    assert (Hinter: forall us cs, kugfrag env (Union us) = true -> esize (Union us) <= esize t ->
        gfrag env (Intersection cs) = true -> esize (Intersection cs) <= esize a -> answers (Union us) (Intersection cs)).
    { intros us cs Hus Hsz Hcs Hsza.
      apply (union_target_intersection_answers env wf us cs (kcomponents_no_vars us Hus) (gfrag_components_no_vars env cs Hcs)).
      - intros C Hc. pose proof (esize_in cs C Hc).
        exact (IH (esize (Union us) + esize C) ltac:(cbn [esize] in Hsza; lia) (Union us) C eq_refl Hus
            (gfrag_kugfrag env C (intersection_component_gfrag cs C Hcs Hc))).
      - intros C Hc. pose proof (esize_in us C Hc).
        exact (IH (esize C + esize (Intersection cs)) ltac:(cbn [esize] in Hsz; lia) C (Intersection cs) eq_refl
            (gfrag_kugfrag env C (kcomponent_gfrag us C Hus Hc)) (gfrag_kugfrag env _ Hcs)). }
    destruct (kugfrag_cases env t Ht) as [Gt|[[ts [-> [_ Hts]]]|[ts [-> [_ Hts]]]]].
    - (* t of gfrag *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + exact (gfrag_answers t a Gt Ga).
      + (* a union assignee *)
        destruct (gfrag_cases env t Gt) as [[m [c [args Et]]]|[[t' [Et _]]|[[gm [nn [p [vs [Et _]]]]]|[cs Et]]]]; subst t;
            try (apply (Hflip ys Ha (le_n _)); exact I).
        (* an intersection target: each of its components *)
        apply (intersection_target_answers env wf cs (Union ys) (gfrag_components_no_vars env cs Gt) Hva I).
        intros C Hc. pose proof (esize_in cs C Hc).
        exact (IH (esize C + esize (Union ys)) ltac:(cbn [esize]; lia) C (Union ys) eq_refl (gfrag_kugfrag env C (intersection_component_gfrag cs C Gt Hc)) Ha).
      + (* a nullable union assignee: rejected, or taken by what the target wraps *)
        destruct (gfrag_cases env t Gt) as [[m [c [args Et]]]|[[t' [Et [Hnn Gt']]]|[[gm [nn [p [vs [Et _]]]]]|[cs Et]]]]; subst t.
        * exists 1. discriminate.
        * destruct (IH (esize t' + esize (Union ys)) ltac:(cbn [esize]; lia) t' (Union ys) eq_refl (gfrag_kugfrag env t' Gt') Ha) as [n Hn].
          exists (S n). exact Hn.
        * exists 1. discriminate.
        * destruct (is_nullable env (Intersection cs)) eqn:En.
          2: { exists 1. unfold is_assignable_to, empty_unification. rewrite (step_inter_nullable env 0 cs _ [] En). discriminate. }
          apply (intersection_target_answers env wf cs _ (gfrag_components_no_vars env cs Gt) Hva En).
          intros C Hc. pose proof (intersection_component_shape cs C Gt Hc) as Hsh. pose proof (esize_in cs C Hc).
          destruct C as [m c args|c'|g|me msg|v o c'|g|cs'|us]; try contradiction.
          { exists 1. discriminate. }
          { destruct (IH (esize c' + esize (Union ys)) ltac:(cbn [esize] in *; lia) c' (Union ys) eq_refl
                (gfrag_kugfrag env c' (gfrag_nullable_inner env c' (intersection_component_gfrag cs _ Gt Hc))) Ha) as [n Hn].
            exists (S n). exact Hn. }
          { destruct g. exists 1. discriminate. }
    - (* t a union *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + destruct (gfrag_cases env a Ga) as [[m [c [args Ea]]]|[[a' [Ea _]]|[[gm [nn [p [vs [Ea _]]]]]|[cs Ea]]]]; subst a;
            try (apply (Hsearch ts Ht (le_n _)); exact I).
        exact (Hinter ts cs Ht (le_n _) Ga (le_n _)).
      + apply (Hflip ys Ha (le_n _)). exact I.
      + apply (Hsearch ts Ht (le_n _)). exact I.
    - (* t a nullable union: the union takes the assignee without null *)
      destruct (kugfrag_cases env a Ha) as [Ga|[[ys [-> [_ Hys]]]|[ys [-> [_ Hys]]]]].
      + pose proof (esize_without_null a) as Hsz. apply (nullable_target_answers env (Union ts) a Ga).
        exact (IH (esize (Union ts) + esize (without_null env a)) ltac:(cbn [esize]; lia) (Union ts) (without_null env a) eq_refl Ht
            (gfrag_kugfrag env _ (gfrag_without_null env wf declared declared_wf a Ga))).
      + apply (Hflip ys Ha (le_n _)). exact I.
      + destruct (IH (esize (Union ts) + esize (Union ys)) ltac:(cbn [esize]; lia) (Union ts) (Union ys) eq_refl Ht Ha) as [n Hn].
        exists (S n). exact Hn.
Qed.

(* Transitivity, as usual, where unify terminates (Conjectures.transitivity_terminating, with unions) *)
Theorem transitivity_terminating_with_unions: forall n1 n2 x y z,
    ugfrag env x = true -> ugfrag env y = true -> ugfrag env z = true ->
    refs_wf env declared x -> refs_wf env declared y -> refs_wf env declared z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    exists n, is_assignable_to env n x z = Some true.
Proof.
    intros n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2.
    apply (never_fails_answers env x z (transitivity_never_fails_with_unions n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2)).
    exact (kugfrag_terminates z x (ugfrag_kugfrag env z Hz) (ugfrag_kugfrag env x Hx)).
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

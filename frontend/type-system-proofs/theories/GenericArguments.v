From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Ops.
From EmergeTypeSystem Require Import Ownership.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Substitution.
From EmergeTypeSystem Require Import Inference.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From EmergeTypeSystem Require Import Conjectures.
From EmergeTypeSystem Require Import MemberCalls.
From EmergeTypeSystem Require Import FinalValues.
From EmergeTypeSystem Require Import FreeInstances.
From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Inference with the type parameters of the caller in the arguments                              *)
(*                                                                                                *)
(* Generic code calls functions, too: the types of its arguments mention its own type parameters  *)
(* (`T`, `T?`, `Box<T>`, `T & A`), and so may the final values inference picks. Constraints.v and *)
(* MemberCalls.v take arguments of class types; this repeats them for arguments of the fragment   *)
(* of Generics.v (generic_arguments, generic_invocation_sound), whose variable bounds and final   *)
(* values are of that fragment, too. As in FinalValues.v, that rests on the conjectures of        *)
(* Conjectures.v: intersect and closestCommonSupertypeWith build types of the fragment, below and *)
(* above both of their operands, and unify terminates where inheritance isn't expansive. Calling  *)
(* a member function in generic code is then sound for the types of the generic code              *)
(* (member_call_in_generic_code_sound); GenericCode.v carries that over to its instances.         *)
(*                                                                                                *)
(* Of the arguments, this takes Nothing only as `exclusive Nothing` (bottom_only): unify takes a  *)
(* reference to a type parameter bounded by Nothing, and an intersection of unrelated classes,    *)
(* for Nothing, and neither has values. The type parameters of the caller are none of those       *)
(* inferred (owners_free, for the ownership of type arguments). Whatever else holds of the        *)
(* arguments and of the bounds is carried along as Qb, and Qa for type arguments: it holds of the *)
(* parts of the arguments, and intersect and closestCommonSupertypeWith keep it. GenericCode.v    *)
(* makes it the types of generic code. The receiver still is of a class type, without the type    *)
(* parameters of the caller.                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

Section GenericArguments.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_nothing_as_bottom := wf_supertypes_mention_nothing_as_bottom env wf.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

(* The conjectures of Conjectures.v *)
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis tame: tame_inheritance env.
Hypothesis intersect_in_fragment: intersect_stays_in_fragment env declared.
Hypothesis supertype_in_fragment: closest_common_supertype_stays_in_fragment env declared.
Hypothesis intersect_below: intersect_is_below_both env declared.
Hypothesis supertype_above: closest_common_supertype_is_above_both env declared.

(* ---------------------------------------------------------------------------------------------- *)
(* Assignability on the fragment of Generics.v                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Definition of_fragment (t: EType): Prop := gfrag env t = true /\ refs_wf env declared t.

(* What the types of the arguments and the bounds of the type variables are, besides: closed under
   taking their parts, and under intersect and closestCommonSupertypeWith *)
Variable Qb: EType -> Prop.

(* and of the type arguments, whose types are of Qb *)
Variable Qa: EType -> Prop.
Hypothesis Qa_nested: forall v o n, Qa (TypeArgument v o n) -> Qb n.

Hypothesis Qb_intersect: forall a c, of_fragment a -> of_fragment c -> Qb a -> Qb c -> Qb (intersect env a c).
Hypothesis Qb_supertype: forall a c, of_fragment a -> of_fragment c -> Qb a -> Qb c -> Qb (closest_common_supertype_with env a c).
Hypothesis Qb_top: Qb top_type.
Hypothesis Qb_bottom: Qb bottom_type.
Hypothesis Qb_any: forall m, Qb (RootResolved (Some m) any []).
Hypothesis Qb_root: forall m c args a, Qb (RootResolved m c args) -> In a args -> Qa a.
Hypothesis Qb_nullable: forall n, Qb (Nullable n) -> Qb n.
Hypothesis Qb_bound: forall g, Qb (Generic g) -> Qb (effective_bound env g).
Hypothesis Qb_narrowed: forall g, Qb (Generic g) -> Qb (without_null env (Generic g)).
Hypothesis Qb_component: forall cs c, Qb (Intersection cs) -> In c cs -> Qb c.
Hypothesis Qb_nullable_component: forall cs c, Qb (Nullable (Intersection cs)) -> In c cs -> Qb (Nullable c).
Hypothesis Qb_supertype_arguments: forall sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> Qa x) ->
    forall a, In a (parameterized_supertype_arguments env sub xs super) -> Qa a.

(* x is assignable to y *)
Definition below (x y: EType): Prop := exists n, unify env n y x (Ongoing []) = Some (Ongoing []).

Lemma of_fragment_no_vars: forall t, of_fragment t -> no_vars t = true.
Proof. intros t [H _]. exact (gfrag_no_vars env t H). Qed.

Lemma below_at: forall x y s, of_fragment x -> of_fragment y -> below x y ->
    exists n, unify env n y x (Ongoing s) = Some (Ongoing s).
Proof.
    intros x y s Hx Hy [n Hn]. exists n.
    exact (gat_states env wf n y x [] s (of_fragment_no_vars y Hy) (of_fragment_no_vars x Hx) Hn).
Qed.

Lemma below_never_fails: forall x y, of_fragment x -> of_fragment y -> below x y -> never_fails env y x.
Proof.
    intros x y Hx Hy [n Hn]. exact (success_never_fails env wf n y x [] (of_fragment_no_vars y Hy) (of_fragment_no_vars x Hx) Hn).
Qed.

(* Where unify terminates, it accepts what it never rejects *)
Lemma gaccepts: forall x y, of_fragment x -> of_fragment y -> never_fails env y x -> below x y.
Proof.
    intros x y [Hx Hrx] [Hy Hry] Hnf.
    destruct (terminates env declared wf declared_wf finite tame y x [] Hy Hx Hry Hrx) as [n Hn].
    exists n. specialize (Hnf n []).
    destruct (unify env n y x (Ongoing [])) as [[u|]|] eqn:E; [|contradiction Hnf; reflexivity|contradiction Hn; reflexivity].
    rewrite (gkeeps env wf n y x [] u Hy Hx E). reflexivity.
Qed.

Lemma assignable_below: forall n x y, gfrag env x = true -> gfrag env y = true -> is_assignable_to env n x y = Some true -> below x y.
Proof.
    intros n x y Hx Hy H. exists n. unfold is_assignable_to, empty_unification in H.
    destruct (unify env n y x (Ongoing [])) as [[u|]|] eqn:E; simpl in H; try discriminate H.
    rewrite (gkeeps env wf n y x [] u Hy Hx E). reflexivity.
Qed.

Lemma below_trans: forall x y z, of_fragment x -> of_fragment y -> of_fragment z -> below x y -> below y z -> below x z.
Proof.
    intros x y z [Hx Hrx] [Hy Hry] [Hz Hrz] [n1 H1] [n2 H2].
    destruct (transitivity_terminating env wf declared declared_wf terminates finite tame n1 n2 x y z Hx Hy Hz Hrx Hry Hrz)
        as [f Hf].
    - unfold is_assignable_to, empty_unification. rewrite H1. reflexivity.
    - unfold is_assignable_to, empty_unification. rewrite H2. reflexivity.
    - exact (assignable_below f x z Hx Hz Hf).
Qed.

Lemma below_refl: forall x, of_fragment x -> below x x.
Proof. intros x Hx. exact (gaccepts x x Hx Hx (reflexive_never_fails env wf x (proj1 Hx))). Qed.

Lemma top_of_fragment: of_fragment top_type.
Proof. split; [exact (top_gfrag env wf)|exact I]. Qed.

Lemma bottom_of_fragment: of_fragment bottom_type.
Proof. split; [exact (bottom_gfrag env wf)|exact I]. Qed.

Lemma below_bottom: forall x, of_fragment x -> below bottom_type x.
Proof.
    intros x Hx. destruct (below_refl bottom_type bottom_of_fragment) as [n Hn].
    apply gaccepts; [exact bottom_of_fragment|exact Hx|].
    exact (below_bottom_never_fails env wf declared declared_wf n bottom_type [] (bottom_gfrag env wf) Hn x (proj1 Hx)).
Qed.

Lemma below_top: forall x, of_fragment x -> below x top_type.
Proof.
    intros x Hx. destruct (below_refl top_type top_of_fragment) as [n Hn].
    apply gaccepts; [exact Hx|exact top_of_fragment|].
    exact (above_top_never_fails env wf declared declared_wf n top_type [] (top_gfrag env wf) Hn x (proj1 Hx)).
Qed.

(* An intersection is assignable to each of its components *)
Lemma intersection_below_component: forall cs c, of_fragment (Intersection cs) -> In c cs -> below (Intersection cs) c.
Proof.
    intros cs c [H Hr] Hc. destruct (intersection_gfrag env cs H) as [_ Hcs]. destruct (Hcs c Hc) as [Hcomp Hgc].
    apply gaccepts; [split; [exact H|exact Hr]|split; [exact Hgc|exact I]|].
    apply never_fails_step. intros f s.
    destruct (component_cases env c Hcomp Hgc) as [[m [d [args ->]]]|[gm [nn [p [bound [-> _]]]]]];
        [rewrite step_root_inter|rewrite step_generic_inter]; apply (flipped_never_fails env f _ cs s _ Hc);
        exact (reflexive_never_fails env wf _ Hgc f s).
Qed.

(* What is assignable to each component of an intersection is assignable to the intersection *)
Lemma below_intersection_of: forall x cs, of_fragment x -> of_fragment (Intersection cs) -> is_nullable env x = false ->
    (forall c, In c cs -> below x c) -> below x (Intersection cs).
Proof.
    intros x cs Hx Hi Hn H. apply gaccepts; [exact Hx|exact Hi|].
    destruct (intersection_gfrag env cs (proj1 Hi)) as [_ Hcs].
    apply (inter_target_never_fails env wf); [| exact (of_fragment_no_vars x Hx) | |].
    - apply forallb_forall. intros c Hc. exact (gfrag_no_vars env c (proj2 (Hcs c Hc))).
    - destruct (gfrag_cases env x (proj1 Hx)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [exact I|discriminate Hn|exact I|exact I].
    - intros c Hc. destruct (H c Hc) as [n E].
      exact (success_never_fails env wf n c x [] (gfrag_no_vars env c (proj2 (Hcs c Hc))) (of_fragment_no_vars x Hx) E).
Qed.

(* What the bounds of type variables are made with: closest common supertypes and intersections *)
Lemma supertype_of_fragment: forall a b, of_fragment a -> of_fragment b -> of_fragment (closest_common_supertype_with env a b).
Proof. intros a b Ha Hb. exact (supertype_in_fragment a b Ha Hb). Qed.

Lemma intersect_of_fragment: forall a b, of_fragment a -> of_fragment b -> of_fragment (intersect env a b).
Proof. intros a b Ha Hb. exact (intersect_in_fragment a b Ha Hb). Qed.

Lemma below_supertype: forall a b, of_fragment a -> of_fragment b ->
    below a (closest_common_supertype_with env a b) /\ below b (closest_common_supertype_with env a b).
Proof.
    intros a b Ha Hb. destruct (supertype_of_fragment a b Ha Hb) as [Hs _].
    destruct (supertype_above a b Ha Hb) as [[n1 H1] [n2 H2]].
    split; [exact (assignable_below n1 _ _ (proj1 Ha) Hs H1)|exact (assignable_below n2 _ _ (proj1 Hb) Hs H2)].
Qed.

Lemma intersect_below_both: forall a b, of_fragment a -> of_fragment b ->
    below (intersect env a b) a /\ below (intersect env a b) b.
Proof.
    intros a b Ha Hb. destruct (intersect_of_fragment a b Ha Hb) as [Hi _].
    destruct (intersect_below a b Ha Hb) as [[n1 H1] [n2 H2]].
    split; [exact (assignable_below n1 _ _ Hi (proj1 Ha) H1)|exact (assignable_below n2 _ _ Hi (proj1 Hb) H2)].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The types of the arguments                                                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* Nothing only as `exclusive Nothing`: no other type without values, no reference to a type
   parameter bounded by Nothing, nor an intersection of unrelated classes, which unify takes for
   Nothing (is_non_nullable_nothing). Of a reference, its effective bound isn't Nothing, which
   covers its top, and its declared bound below that (see Subtyping.through_param), taken from
   bound_bottom_only *)
Fixpoint bottom_only_h (bound_bottom_only: TypeParameterId -> bool) (t: EType): bool :=
    match t with
    | RootResolved m c arguments =>
        (if class_eqb c nothing then is_bottom m arguments else true) && forallb (bottom_only_h bound_bottom_only) arguments
    | Nullable n => bottom_only_h bound_bottom_only n
    | TypeArgument _ _ n => bottom_only_h bound_bottom_only n
    | Generic g => negb (is_non_nullable_nothing env (without_null env (effective_bound env g))) && bound_bottom_only (param_of g)
    | Intersection cs => negb (is_non_nullable_nothing env (Intersection cs)) && forallb (bottom_only_h bound_bottom_only) cs
    | _ => true
    end.

Definition param_bottom_only (p: TypeParameterId): bool := through_param env bottom_only_h true p.

Fixpoint bottom_only (t: EType): bool :=
    match t with
    | RootResolved m c arguments => (if class_eqb c nothing then is_bottom m arguments else true) && forallb bottom_only arguments
    | Nullable n => bottom_only n
    | TypeArgument _ _ n => bottom_only n
    | Generic g => negb (is_non_nullable_nothing env (without_null env (effective_bound env g))) && param_bottom_only (param_of g)
    | Intersection cs => negb (is_non_nullable_nothing env (Intersection cs)) && forallb bottom_only cs
    | _ => true
    end.

Let deep := wf_bounds_deep_ranked env wf.

(* Conjecture: closestCommonSupertypeWith of two types that mention Nothing only as
   `exclusive Nothing` mentions it only so; it is above both (closest_common_supertype_is_above_both),
   and its type arguments are combined of theirs *)
Definition closest_common_supertype_keeps_bottom_only: Prop :=
    forall a c, of_fragment a -> of_fragment c -> bottom_only a = true -> bottom_only c = true ->
        bottom_only (closest_common_supertype_with env a c) = true.

Hypothesis supertype_bottom_only: closest_common_supertype_keeps_bottom_only.

Lemma bottom_only_top: forall t, bottom_only t = bottom_only_h param_bottom_only t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity; try exact (IH n).
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma bottom_only_h_agree: forall p k U1 U2, (forall q, q = p \/ parameter_rank env q < k -> U1 q = U2 q) ->
    forall t, deep_ranked env p k t = true -> bottom_only_h U1 t = bottom_only_h U2 t.
Proof.
    intros p k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity; try exact (IH n Ht).
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - rewrite (HU _ (deep_ranked_param env p k g Ht)). reflexivity.
    - f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma bottom_only_h_mono: forall U1 U2, (forall q, U1 q = true -> U2 q = true) ->
    forall t, bottom_only_h U1 t = true -> bottom_only_h U2 t = true.
Proof.
    intros U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try exact Ht; try exact (IH n Ht).
    - apply andb_true_iff in Ht. destruct Ht as [Hc Ha]. rewrite Hc. cbn [andb]. clear Hc.
      induction args as [|a args IHa]; [reflexivity|]. simpl in Ha |- *. apply andb_true_iff in Ha.
      rewrite (IH a (proj1 Ha)), (IHa (proj2 Ha)). reflexivity.
    - apply andb_true_iff in Ht. destruct Ht as [Hn Hp]. rewrite Hn, (HU _ Hp). reflexivity.
    - apply andb_true_iff in Ht. destruct Ht as [Hn Ha]. rewrite Hn. cbn [andb]. clear Hn.
      induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ha |- *. apply andb_true_iff in Ha.
      rewrite (IH c (proj1 Ha)), (IHc (proj2 Ha)). reflexivity.
Qed.

Lemma param_bottom_only_eq: forall p, param_bottom_only p = bottom_only (parameter_bound env p).
Proof.
    intros p. rewrite bottom_only_top. unfold param_bottom_only at 1.
    exact (through_param_fix env bottom_only_h deep bottom_only_h_agree (fun U1 U2 t H => bottom_only_h_mono U1 U2 H t) p).
Qed.

(* What is Nothing only as `exclusive Nothing` below the top of a type, and in the declared bounds of
   the parameters of the references at its top *)
Fixpoint bottom_rest (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb bottom_only arguments
    | Nullable n => bottom_rest n
    | Generic g => param_bottom_only (param_of g)
    | Intersection cs => forallb bottom_rest cs
    | _ => true
    end.

Lemma bottom_only_rest: forall t, bottom_only t = true -> bottom_rest t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity.
    - apply andb_true_iff in H. exact (proj2 H).
    - exact (IH n H).
    - apply andb_true_iff in H. exact (proj2 H).
    - apply andb_true_iff in H. destruct H as [_ H]. induction cs as [|c cs IHc]; [reflexivity|].
      simpl in H |- *. apply andb_true_iff in H. rewrite (IH c (proj1 H)), (IHc (proj2 H)). reflexivity.
Qed.

Lemma bottom_rest_with_mutability: forall m t, bottom_rest (with_mutability env m t) = bottom_rest t.
Proof.
    fix IH 2. intros m [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; try reflexivity.
    - cbn [with_mutability]. change (bottom_rest (Nullable n)) with (bottom_rest n). rewrite <- (IH m n).
      destruct (with_mutability env m n); reflexivity.
    - simpl. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly).
      intros k. clear m. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH k c), IHc. reflexivity.
Qed.

(* Where the top of a type isn't Nothing, a type with Nothing only as `exclusive Nothing` below its
   top has it only so: at its top, a reference whose effective bound isn't Nothing, an intersection
   none of whose components is Nothing *)
Lemma bottom_only_top_checks: forall t, gfrag env t = true -> bottom_rest t = true ->
    is_non_nullable_nothing env (without_null env t) = false -> bottom_only t = true /\ bottom_only (without_null env t) = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] Hf Hr Hn; simpl in Hf; try discriminate Hf.
    - simpl in Hr, Hn |- *. rewrite Hn, Hr. split; reflexivity.
    - apply andb_true_iff in Hf. exact (IH n (proj2 Hf) Hr Hn).
    - destruct vs; [|discriminate Hf]. simpl in Hr.
      assert (E: is_non_nullable_nothing env (without_null env (effective_bound env (mkGenericRef gm nn p [])))
          = is_non_nullable_nothing env (without_null env (Generic (mkGenericRef gm nn p [])))).
      { rewrite (without_null_generic env), (non_nullable_nothing_generic env ranked). unfold narrow_ref.
        cbn [given_mutability is_narrowed param_of variables_of]. rewrite (effective_bound_narrowed env ranked). reflexivity. }
      split.
      + change (negb (is_non_nullable_nothing env (without_null env (effective_bound env (mkGenericRef gm nn p [])))) && param_bottom_only p = true).
        rewrite E, Hn, Hr. reflexivity.
      + rewrite (without_null_generic env). unfold narrow_ref. cbn [given_mutability is_narrowed param_of variables_of].
        change (negb (is_non_nullable_nothing env (without_null env (effective_bound env
            (mkGenericRef gm (nn || is_nullable env (Generic (mkGenericRef gm nn p []))) p [])))) && param_bottom_only p = true).
        rewrite (effective_bound_narrowed env ranked), (without_null_twice_any env), E, Hn, Hr. reflexivity.
    - assert (Hw: without_null env (Intersection cs) = Intersection cs)
          by exact (without_null_not_nullable_intersection env cs (gfrag_intersection_not_nullable env cs Hf)).
      rewrite Hw in Hn |- *.
      apply andb_true_iff in Hf. destruct Hf as [Hf _]. apply andb_true_iff in Hf. destruct Hf as [_ Hcs]. simpl in Hn, Hr.
      assert (Hall: forallb bottom_only cs = true).
      { apply orb_false_iff in Hn. destruct Hn as [Hn _]. clear -IH Hcs Hr Hn wf declared_wf.
        induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hcs, Hr, Hn |- *.
        apply andb_true_iff in Hcs, Hr. apply orb_false_iff in Hn. destruct Hcs as [Hc Hcs]. apply andb_true_iff in Hc.
        destruct Hc as [Hcomp Hc]. rewrite (IHc Hcs (proj2 Hr) (proj2 Hn)), andb_true_r.
        pose proof (component_not_nullable env c Hcomp) as Hnn.
        refine (proj1 (IH c Hc (proj1 Hr) _)). rewrite (without_null_unchanged env c Hnn). exact (proj1 Hn). }
      assert (H: bottom_only (Intersection cs) = true) by (simpl; rewrite Hn, Hall; reflexivity).
      split; exact H.
Qed.

Lemma bottom_only_generic: forall g, variables_of g = [] -> bottom_only (Generic g) = true ->
    is_non_nullable_nothing env (without_null env (effective_bound env g)) = false /\ bottom_only (effective_bound env g) = true.
Proof.
    intros [gm nn p vs] Hv H. cbn [variables_of] in Hv. subst vs. simpl in H. apply andb_true_iff in H. destruct H as [Hn Hp].
    apply negb_true_iff in Hn. split; [exact Hn|]. rewrite param_bottom_only_eq in Hp.
    pose proof (bottom_only_rest _ Hp) as Hr. pose proof (parameter_bound_gfrag env declared declared_wf p) as Hf.
    rewrite (effective_bound_eq env ranked) in Hn |- *. cbn [with_type_variables variables_of given_mutability is_narrowed param_of] in Hn |- *.
    destruct gm as [m|].
    - pose proof (gfrag_with_mutability env wf declared declared_wf m _ Hf) as Hfm. rewrite <- (bottom_rest_with_mutability m) in Hr.
      destruct nn; [rewrite (without_null_twice_any env) in Hn|];
          destruct (bottom_only_top_checks _ Hfm Hr Hn) as [H1 H2]; assumption.
    - destruct nn; [rewrite (without_null_twice_any env) in Hn|];
          destruct (bottom_only_top_checks _ Hf Hr Hn) as [H1 H2]; assumption.
Qed.

(* The ownership of a type parameter of the caller: none of the type parameters inferred *)
Definition ownership_free (b: Bindings) (o: Ownership): Prop :=
    match o with parameter_ownership q => lookup_binding b q = None | _ => True end.

(* Of a reference, the ownerships in the declared bound of its parameter (see Subtyping.through_param),
   taken from bound_owners_free *)
Fixpoint owners_free_h (b: Bindings) (bound_owners_free: TypeParameterId -> Prop) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => owners_free_h b bound_owners_free a /\ acc) True arguments
    | Nullable n => owners_free_h b bound_owners_free n
    | Generic g => bound_owners_free (param_of g)
    | TypeArgument _ o n => ownership_free b o /\ owners_free_h b bound_owners_free n
    | Intersection cs => fold_right (fun c acc => owners_free_h b bound_owners_free c /\ acc) True cs
    | _ => True
    end.

Definition param_owners_free (b: Bindings) (p: TypeParameterId): Prop := through_param env (owners_free_h b) True p.

Fixpoint owners_free (b: Bindings) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => owners_free b a /\ acc) True arguments
    | Nullable n => owners_free b n
    | Generic g => param_owners_free b (param_of g)
    | TypeArgument _ o n => ownership_free b o /\ owners_free b n
    | Intersection cs => fold_right (fun c acc => owners_free b c /\ acc) True cs
    | _ => True
    end.

Lemma owners_free_top: forall b t, owners_free b t = owners_free_h b (param_owners_free b) t.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity; try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma owners_free_h_agree: forall b p k U1 U2, (forall q, q = p \/ parameter_rank env q < k -> U1 q = U2 q) ->
    forall t, deep_ranked env p k t = true -> owners_free_h b U1 t = owners_free_h b U2 t.
Proof.
    intros b p k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity; try exact (IH n Ht).
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - exact (HU _ (deep_ranked_param env p k g Ht)).
    - rewrite (IH n Ht). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma owners_free_h_mono: forall b U1 U2, (forall q, U1 q -> U2 q) -> forall t, owners_free_h b U1 t -> owners_free_h b U2 t.
Proof.
    intros b U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try exact Ht; try exact (IH n Ht).
    - induction args as [|a args IHa]; [exact I|]. destruct Ht as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (HU _ Ht).
    - destruct Ht as [Ho Hn]. exact (conj Ho (IH n Hn)).
    - induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

Lemma param_owners_free_iff: forall b p, param_owners_free b p <-> owners_free b (parameter_bound env p).
Proof.
    intros b p. rewrite owners_free_top. unfold param_owners_free at 1.
    exact (through_param_fix_prop env (owners_free_h b) deep (owners_free_h_agree b) (fun U1 U2 t H => owners_free_h_mono b U1 U2 H t) p).
Qed.

(* A mutability applied, or null removed, the ownerships stay *)
Lemma owners_free_adjust: forall b t,
    (forall m, owners_free b (with_mutability env m t) <-> owners_free b t) /\ (owners_free b (without_null env t) <-> owners_free b t).
Proof.
    intros b. fix IH 1. intros [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; split; try intros m; try reflexivity.
    - cbn [with_mutability]. change (owners_free b (Nullable n)) with (owners_free b n). rewrite <- (proj1 (IH n) m).
      destruct (with_mutability env m n); reflexivity.
    - exact (proj2 (IH n)).
    - simpl. rewrite (proj1 (IH n) m). reflexivity.
    - simpl. rewrite (proj2 (IH n)). reflexivity.
    - simpl. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability env (with_mutability env m c)) cs) readonly).
      intros k. clear m. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj1 (IH c) k), IHc. reflexivity.
    - cbn [without_null]. destruct (forallb _ cs); [|reflexivity]. simpl.
      induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (proj2 (IH c)), IHc. reflexivity.
Qed.

Lemma owners_free_generic: forall b g, variables_of g = [] -> owners_free b (Generic g) <-> owners_free b (effective_bound env g).
Proof.
    intros b [gm nn p vs] Hv. cbn [variables_of] in Hv. subst vs. change (owners_free b (Generic (mkGenericRef gm nn p [])))
        with (param_owners_free b p). rewrite param_owners_free_iff, (effective_bound_eq env ranked).
    cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
    destruct gm as [m|], nn; cbn iota; rewrite ?(proj2 (owners_free_adjust b _)), ?(proj1 (owners_free_adjust b _)); reflexivity.
Qed.

Definition yfrag (b: Bindings) (t: EType): Prop := of_fragment t /\ bottom_only t = true /\ owners_free b t /\ Qb t.

Definition argument_yfrag (b: Bindings) (a: EType): Prop :=
    argument_gfrag env a = true /\ refs_wf env declared a /\ bottom_only a = true /\ owners_free b a /\ Qa a.

Lemma ownership_kept: forall b oa ot, ownership_is_assignable_to oa ot = true -> ownership_free b oa ->
    ownership_is_assignable_to oa (instantiate_ownership b ot) = true.
Proof.
    intros b oa ot H Hf. destruct ot as [| | |p]; try exact H.
    destruct oa as [| | |q]; try discriminate H. simpl in H, Hf |- *. apply param_eqb_eq in H. subst q. rewrite Hf. reflexivity.
Qed.

Lemma nothing_without_null: forall t, gfrag env t = true -> is_non_nullable_nothing env t = true ->
    is_non_nullable_nothing env (without_null env t) = true.
Proof.
    intros t. destruct (ranked_exists env t) as [r Hr]. revert t Hr. induction r as [r IHr] using lt_wf_ind.
    intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] Hr Hf H; simpl in Hf; try discriminate Hf; try exact H.
    - simpl in H. discriminate H.
    - destruct vs; [|discriminate Hf]. pose proof (ref_ranked env r _ Hr) as Hg.
      destruct (narrowed_ref env wf declared declared_wf gm nn p) as [E _]. rewrite E.
      rewrite (non_nullable_nothing_generic env ranked) in H. rewrite (non_nullable_nothing_generic env ranked).
      rewrite (effective_bound_narrowed env ranked).
      exact (IHr _ Hg _ (effective_bound_ranked env ranked _) (bound_gfrag env wf declared declared_wf (mkGenericRef gm nn p []) eq_refl) H).
    - rewrite (without_null_not_nullable_intersection env cs (gfrag_intersection_not_nullable env cs Hf)). exact H.
Qed.

Lemma bottom_only_without_null: forall t, gfrag env t = true -> bottom_only t = true -> bottom_only (without_null env t) = true.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H Hb; simpl in H; try exact Hb; try discriminate H.
    - apply andb_true_iff in H. exact (IH n (proj2 H) Hb).
    - destruct vs; [|discriminate H]. rewrite (without_null_generic env). unfold narrow_ref.
      cbn [given_mutability is_narrowed param_of variables_of].
      change (negb (is_non_nullable_nothing env (without_null env (effective_bound env
          (mkGenericRef gm (nn || is_nullable env (Generic (mkGenericRef gm nn p []))) p [])))) && param_bottom_only p = true).
      rewrite (effective_bound_narrowed env ranked), (without_null_twice_any env). exact Hb.
    - rewrite (without_null_not_nullable_intersection env cs (gfrag_intersection_not_nullable env cs H)). exact Hb.
Qed.

Lemma owners_free_without_null: forall b t, gfrag env t = true -> owners_free b t -> owners_free b (without_null env t).
Proof. intros b t _ H. apply (proj2 (owners_free_adjust b t)), H. Qed.

(* A type of them that unify takes for Nothing is `exclusive Nothing` *)
Lemma bottom_only_nothing: forall t, gfrag env t = true -> bottom_only t = true ->
    is_non_nullable_nothing env t = true -> t = bottom_type.
Proof.
    intros t Ht Hb Hn.
    destruct (gfrag_cases env t Ht) as [[m [c [args ->]]]|[[n [-> _]]|[[gm [nn [p [bd [-> Hbd]]]]]|[cs ->]]]].
    - simpl in Hb, Hn. rewrite Hn in Hb. apply class_eqb_true in Hn. subst c.
      destruct m as [[]|], args; simpl in Hb; try discriminate Hb. reflexivity.
    - simpl in Hn. discriminate Hn.
    - simpl in Hb. apply andb_true_iff in Hb. destruct Hb as [Hb _]. rewrite (non_nullable_nothing_generic env ranked) in Hn.
      rewrite (nothing_without_null _ (bound_gfrag env wf declared declared_wf _ Ht) Hn) in Hb. discriminate Hb.
    - simpl in Hb, Hn. rewrite Hn in Hb. discriminate Hb.
Qed.

Lemma yfrag_root: forall b m c args, yfrag b (RootResolved m c args) ->
    length args = length (parameter_ids env c) /\ forall a, In a args -> argument_yfrag b a.
Proof.
    intros b m c args [[Hg Hr] [Hb [Ho Hq]]]. destruct (root_gfrag env m c args Hg) as [Hl Ha]. split; [exact Hl|].
    intros a Hin. split; [exact (Ha a Hin)|]. split; [exact I|].
    split; [simpl in Hb; apply andb_true_iff in Hb; rewrite forallb_forall in Hb; exact (proj2 Hb a Hin)|].
    split; [exact (fold_and_in (owners_free b) args Ho a Hin)|exact (Qb_root m c args a Hq Hin)].
Qed.

Lemma yfrag_nullable: forall b n, yfrag b (Nullable n) -> yfrag b n /\ non_null env n = true.
Proof.
    intros b n [[Hg Hr] [Hb [Ho Hq]]]. simpl in Hg. apply andb_true_iff in Hg. destruct Hg as [Hnn Hg].
    split; [split; [split; [exact Hg|exact Hr]|split; [exact Hb|split; [exact Ho|exact (Qb_nullable n Hq)]]]|exact Hnn].
Qed.

Lemma yfrag_generic: forall b g, yfrag b (Generic g) -> yfrag b (effective_bound env g).
Proof.
    intros b g [[Hg _] [Hb [Ho Hq]]]. assert (Hv: variables_of g = []) by (destruct g as [? ? ? [|? ?]]; [reflexivity|discriminate Hg]).
    destruct (bottom_only_generic g Hv Hb) as [_ Hb']. apply (owners_free_generic b g Hv) in Ho.
    split; [split; [exact (bound_gfrag env wf declared declared_wf g Hg)|exact I]|].
    split; [exact Hb'|split; [exact Ho|exact (Qb_bound g Hq)]].
Qed.

Lemma yfrag_component: forall b cs c, yfrag b (Intersection cs) -> In c cs -> yfrag b c /\ is_component env c = true.
Proof.
    intros b cs c [[Hg Hr] [Hb [Ho Hq]]] Hc. destruct (intersection_gfrag env cs Hg) as [_ Hcs]. destruct (Hcs c Hc) as [Hcomp Hgc].
    simpl in Hb. apply andb_true_iff in Hb. destruct Hb as [_ Hb]. rewrite forallb_forall in Hb.
    split; [|exact Hcomp]. split; [split; [exact Hgc|exact I]|].
    split; [exact (Hb c Hc)|split; [exact (fold_and_in (owners_free b) cs Ho c Hc)|exact (Qb_component cs c Hq Hc)]].
Qed.

Lemma yfrag_without_null: forall b g, yfrag b (Generic g) -> yfrag b (without_null env (Generic g)).
Proof.
    intros b g [[Hg Hr] [Hb [Ho Hq]]]. split; [split|split; [|split]].
    - exact (gfrag_without_null env _ Hg).
    - exact I.
    - exact (bottom_only_without_null _ Hg Hb).
    - exact (owners_free_without_null b _ Hg Ho).
    - exact (Qb_narrowed g Hq).
Qed.

Lemma yfrag_argument: forall b v o n, argument_yfrag b (TypeArgument v o n) -> yfrag b n /\ ownership_free b o.
Proof.
    intros b v o n [Hg [Hr [Hb [[Ho Hn] Hq]]]]. split; [|exact Ho].
    split; [split; [exact Hg|exact Hr]|split; [exact Hb|split; [exact Hn|exact (Qa_nested v o n Hq)]]].
Qed.

Lemma yfrag_top: forall b, yfrag b top_type.
Proof. intros b. split; [exact top_of_fragment|split; [reflexivity|split; [exact I|exact Qb_top]]]. Qed.

Lemma yfrag_bottom: forall b, yfrag b bottom_type.
Proof. intros b. split; [exact bottom_of_fragment|split; [reflexivity|split; [exact I|exact Qb_bottom]]]. Qed.

Lemma yfrag_of_fragment: forall b t, yfrag b t -> of_fragment t.
Proof. intros b t H. exact (proj1 H). Qed.

(* The type arguments of supertypes, made of those of a subclass *)
Section Templates.

Variable b: Bindings.
Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> is_type_argument y = true /\ bottom_only y = true /\ owners_free b y.

Lemma template_instances_yfrag: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> nothing_is_bottom t = true ->
        bottom_only (instantiate env (bindings_of env sub ys) t) = true /\ owners_free b (instantiate env (bindings_of env sub ys) t))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> nothing_is_bottom r = true ->
        bottom_only (instantiate env (bindings_of env sub ys) r) = true /\ owners_free b (instantiate env (bindings_of env sub ys) r)).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    set (bS := bindings_of env sub ys).
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k ->
        template_type env sub (RootResolved m c targs) = true -> nothing_is_bottom (RootResolved m c targs) = true ->
        bottom_only (instantiate env bS (RootResolved m c targs)) = true /\ owners_free b (instantiate env bS (RootResolved m c targs))).
    { intros m c targs Hd Ht Hn. destruct (root_template env sub m c targs Ht) as [_ Htargs].
      destruct (nothing_is_bottom_root m c targs Hn) as [Hc Hnargs].
      assert (Hall: forall a, In a targs -> bottom_only (instantiate env bS a) = true /\ owners_free b (instantiate env bS a))
          by (intros a Ha; pose proof (argument_depth_below m c targs a Ha); exact (IHa a ltac:(lia) (Htargs a Ha) (Hnargs a Ha))).
      rewrite instantiate_class. split.
      - simpl. apply andb_true_iff. split.
        + destruct (class_eqb c nothing) eqn:Ec; [|reflexivity].
          specialize (Hc eq_refl). destruct m as [[]|], targs; simpl in Hc; try discriminate Hc. reflexivity.
        + apply forallb_forall. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. exact (proj1 (Hall a Ha)).
      - apply fold_and_map. intros a Ha. exact (proj2 (Hall a Ha)). }
    split.
    - intros t Hd Ht Hn. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + exact (Hroot m c targs Hd Ht Hn).
      + rewrite depth_nullable in Hd. unfold bS. rewrite instantiate_nullable_class, <- instantiate_class.
        exact (Hroot m c targs ltac:(lia) Ht' Hn).
    - intros r Hd Hr Hn. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        destruct (Hys y (nth_error_In _ _ Hy)) as [Hty [Hby Hoy]].
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy Hty). split; [exact Hby|exact Hoy].
      + simpl in Hd, Hn. destruct (IHt n ltac:(lia) Hn' Hn) as [Hb Hon].
        unfold bS. rewrite (instantiate_template_argument env _ v o n Ho (template_shape env sub n Hn')).
        assert (Hof: ownership_free b o) by (destruct o; try exact I; discriminate Ho).
        destruct (mentions_loosely_bound _ n); [destruct v|]; (split; [exact Hb || reflexivity|split; [exact Hof|exact Hon || exact I]]).
Qed.

End Templates.

Lemma supertype_arguments_yfrag: forall b sub super xs,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length xs = length (parameter_ids env sub) -> (forall x, In x xs -> argument_yfrag b x) ->
    length (parameterized_supertype_arguments env sub xs super) = length (parameter_ids env super)
    /\ forall a, In a (parameterized_supertype_arguments env sub xs super) -> argument_yfrag b a.
Proof.
    intros b sub super xs Hne Hn Hbase Hl Hxs.
    assert (Hta: forall x, In x xs -> is_type_argument x = true)
        by (intros x Hx; exact (argument_gfrag_type_argument env x (proj1 (Hxs x Hx)))).
    destruct (supertype_arguments_gfrag env wf sub super xs Hne Hn Hbase Hl (fun x Hx => proj1 (Hxs x Hx))) as [Hls Hg].
    split; [exact Hls|]. intros a Ha. split; [exact (Hg a Ha)|].
    split; [exact I|].
    pose proof (Qb_supertype_arguments sub super xs Hne Hn Hbase Hl (fun x Hx => proj2 (proj2 (proj2 (proj2 (Hxs x Hx))))) a Ha) as HQa.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
    destruct (proj2 (template_instances_yfrag b sub xs Hl
        (fun x Hx => conj (Hta x Hx) (conj (proj1 (proj2 (proj2 (Hxs x Hx)))) (proj1 (proj2 (proj2 (proj2 (Hxs x Hx)))))))
        (argument_depth r)) r (le_n _) (Ht r Hr) (supertypes_mention_nothing_as_bottom sub super r Hr)) as [H1 H2].
    split; [exact H1|split; [exact H2|exact HQa]].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One step of unify, for the types of the arguments                                               *)
(* ---------------------------------------------------------------------------------------------- *)

(* What a nullable type unifies its nested type with *)
Definition nullable_assignee (a: EType): EType :=
    match a with
    | Nullable n => n
    | Generic _ => without_null env a
    | _ => a
    end.

Lemma nullable_target: forall n z A s, gfrag env A = true ->
    unify env (S n) (Nullable z) A (Ongoing s) = unify env n z (nullable_assignee A) (Ongoing s).
Proof.
    intros n z A s HA.
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]]; try reflexivity.
    exact (step_nullable_inter env n z cs s HA).
Qed.

Lemma nullable_assignee_facts: forall A, gfrag env A = true ->
    gfrag env (nullable_assignee A) = true /\ is_nullable env (nullable_assignee A) = false
    /\ nullable_assignee (nullable_assignee A) = nullable_assignee A
    /\ match nullable_assignee A with Nullable _ | Error _ _ => False | _ => True end.
Proof.
    intros A HA. destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> [Hn Ha]]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
    - split; [exact HA|]. split; [reflexivity|]. split; [reflexivity|exact I].
    - cbn [nullable_assignee]. split; [exact Ha|]. split; [exact (non_null_not_nullable env an Hn)|]. split.
      + destruct an; cbn [nullable_assignee];
            first [reflexivity|discriminate Hn|exact (without_null_unchanged env _ (non_null_not_nullable env _ Hn))].
      + destruct an; first [exact I|discriminate Hn].
    - cbn [nullable_assignee]. split; [exact (gfrag_without_null env _ HA)|]. split; [exact (without_null_not_nullable env wf declared declared_wf _ HA)|].
      split; [|exact I].
      change (nullable_assignee (without_null env (Generic (mkGenericRef gm nn q bq))))
          with (without_null env (without_null env (Generic (mkGenericRef gm nn q bq)))).
      exact (without_null_twice env wf declared declared_wf _ HA).
    - split; [exact HA|]. split; [exact (gfrag_intersection_not_nullable env cs HA)|]. split; [reflexivity|exact I].
Qed.

(* A type variable made nullable: what the type it stands for takes without null, that type made
   nullable takes; the type without null where the variable is narrowed *)
Lemma nullable_variable_below: forall (nn: bool) A x, gfrag env A = true -> gfrag env x = true ->
    below (nullable_assignee A) x -> below A (rewrap_nullable (if nn then without_null env x else x)).
Proof.
    intros nn A x HA Hx [f Hf]. destruct (nullable_assignee_facts A HA) as [HgA0 [HnA0 [HiA0 _]]].
    destruct nn.
    - change (below A (rewrap_nullable (without_null env x))).
      destruct (below_without_null env wf declared declared_wf f x _ Hx HgA0 HnA0 Hf) as [f' Hf'].
      assert (Er: rewrap_nullable (without_null env x) = Nullable (without_null env x)).
      { pose proof (without_null_shape env x) as Hs. destruct (without_null env x); try reflexivity; contradiction. }
      exists (S f'). rewrite Er, (nullable_target f' _ A [] HA). exact Hf'.
    - change (below A (rewrap_nullable x)).
      destruct x as [| y | | | | |]; try (exists (S f); cbn [rewrap_nullable]; rewrite (nullable_target f _ A [] HA); exact Hf).
      (* a nullable type: what it wraps takes the argument without null *)
      destruct f as [|f]; [discriminate Hf|]. rewrite (nullable_target f y _ [] HgA0), HiA0 in Hf.
      exists (S f). cbn [rewrap_nullable]. rewrite (nullable_target f y A [] HA). exact Hf.
Qed.

(* What a type takes without null, it takes made nullable *)
Lemma nullable_below: forall A x, gfrag env A = true -> below (nullable_assignee A) x -> below A (rewrap_nullable x).
Proof.
    intros A x HA [f Hf]. destruct (nullable_assignee_facts A HA) as [HgA0 [HnA0 [HiA0 _]]].
    destruct x as [| y | | | | |]; try (exists (S f); cbn [rewrap_nullable]; rewrite (nullable_target f _ A [] HA); exact Hf).
    destruct f as [|f]; [discriminate Hf|]. rewrite (nullable_target f y _ [] HgA0), HiA0 in Hf.
    exists (S f). cbn [rewrap_nullable]. rewrite (nullable_target f y A [] HA). exact Hf.
Qed.

Lemma ref_apply_of_fragment: forall gm nn x, of_fragment x -> of_fragment (ref_apply env gm nn x).
Proof.
    intros gm nn x [Hx _]. split; [|exact I]. unfold ref_apply. cbn zeta.
    destruct gm as [m|]; destruct nn; first [apply (gfrag_without_null env)|idtac];
        first [apply (gfrag_with_mutability env wf declared declared_wf)|idtac]; exact Hx.
Qed.

Lemma ref_apply_not_nullable: forall gm nn x, of_fragment x -> is_nullable env x = false -> is_nullable env (ref_apply env gm nn x) = false.
Proof.
    intros gm nn x Hx Hn. destruct nn.
    - change (ref_apply env gm true x) with (without_null env (ref_apply env gm false x)).
      exact (without_null_not_nullable env wf declared declared_wf _ (proj1 (ref_apply_of_fragment gm false x Hx))).
    - destruct gm as [m|]; [cbn [ref_apply]; rewrite (is_nullable_with_mutability env wf)|]; exact Hn.
Qed.

(* A type variable of a mutability given to it, narrowed or not: what the type it stands for takes,
   that type of the mutability, and without null where the variable is narrowed, takes, where it fits *)
Lemma reference_below: forall gm nn p A x, of_fragment A -> of_fragment x ->
    sfrag env (Generic (mkGenericRef gm nn p [])) = true ->
    (forall m, gm = Some m -> is_subtype_of (assignee_mutability env A) m = true) ->
    (nn = true -> is_nullable env A = true -> is_nullable env (TypeVariable (mkGenericRef gm nn p [])) = true) ->
    below A x -> below A (ref_apply env gm nn x).
Proof.
    intros gm nn p A x HA Hx Hs Hgm Hnul [f Hf].
    apply (gaccepts A _ HA (ref_apply_of_fragment gm nn x Hx)).
    apply (instance_never_fails env wf declared declared_wf f gm nn x A (proj1 Hx) (proj1 HA)); [| |exact Hf].
    - intros m Em. pose proof (Hgm m Em) as E.
      destruct (gfrag_cases env A (proj1 HA)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact E.
    - intros En. subst nn. specialize (Hnul eq_refl). destruct (is_nullable env A) eqn:EA; [|reflexivity].
      rewrite (narrowed_not_nullable env wf gm p Hs) in Hnul. discriminate (Hnul eq_refl).
Qed.

(* A type variable as the assignee: unify takes it as the plain variable, whatever mutability is
   given to it and whether it is narrowed *)
Lemma assignee_plain: forall k A gm nn p bnd s, gfrag env A = true ->
    unify env (S k) A (TypeVariable (mkGenericRef gm nn p bnd)) (Ongoing s)
    = unify env (S k) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s).
Proof.
    intros k A gm nn p bnd s HA.
    destruct (gfrag_cases env A HA) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; reflexivity.
Qed.

(* What a type is assigned to, it is assigned to of a mutability given to it, and without null *)
Lemma assigned_below: forall gm nn x A, of_fragment x -> of_fragment A -> below x A -> below (ref_apply env gm nn x) A.
Proof.
    intros gm nn x A Hx HA [n Hn]. apply (gaccepts _ A (ref_apply_of_fragment gm nn x Hx) HA).
    exact (instance_assigned_never_fails env wf declared declared_wf n gm nn x A (proj1 Hx) (proj1 HA) Hn).
Qed.

(* What is below a type is, made nullable, below the type made nullable *)
Lemma nullable_assigned_below: forall an y, gfrag env (Nullable an) = true -> below y an -> below (rewrap_nullable y) (Nullable an).
Proof.
    intros an y Han [f Hf].
    destruct y as [m c args|y'|g|me msg|v o n|g|cs]; try (exists (S f); cbn [rewrap_nullable]; rewrite unify_nullable_nullable; exact Hf).
    exfalso. destruct f as [|f]; [discriminate Hf|].
    destruct (gfrag_cases env _ Han) as [[? [? [? E]]]|[[an' [E [Hn Han']]]|[[? [? [? [? [E _]]]]]|[? E]]]]; try discriminate E.
    injection E as <-.
    destruct (gfrag_cases env an Han') as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]].
    - rewrite unify_class_nullable in Hf. discriminate Hf.
    - discriminate Hn.
    - rewrite step_generic_nullable in Hf. discriminate Hf.
    - rewrite step_inter_nullable in Hf by gfrag_hyp. discriminate Hf.
Qed.

(* A type of the fragment, without null, made nullable *)
Lemma of_fragment_rewrap_narrowed: forall y, of_fragment y -> of_fragment (rewrap_nullable (without_null env y)).
Proof.
    intros y [Hy _]. split; [|exact I].
    pose proof (gfrag_without_null env _ Hy) as Hw. pose proof (without_null_not_nullable env wf declared declared_wf _ Hy) as Hn.
    pose proof (without_null_shape env y) as Hs. remember (without_null env y) as w eqn:Ew. clear Ew.
    assert (Hr: rewrap_nullable w = Nullable w) by (destruct w; first [contradiction|reflexivity]).
    rewrite Hr. change (non_null env w && gfrag env w = true). rewrite Hw, andb_true_r.
    destruct (gfrag_cases env w Hw) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; try reflexivity.
    - contradiction.
    - cbn [non_null is_component]. rewrite Hn. reflexivity.
    - cbn [non_null]. rewrite Hn. reflexivity.
Qed.

(* ... and a type of the fragment that isn't nullable, made nullable *)
Lemma of_fragment_rewrap_not_nullable: forall y, of_fragment y -> is_nullable env y = false -> of_fragment (rewrap_nullable y).
Proof.
    intros y [Hy _] Hn. split; [|exact I].
    assert (Hr: rewrap_nullable y = Nullable y) by (destruct y; cbn [is_nullable] in Hn; first [discriminate Hn|reflexivity]).
    rewrite Hr. change (non_null env y && gfrag env y = true). rewrite Hy, andb_true_r.
    destruct (gfrag_cases env y Hy) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; try reflexivity.
    - discriminate Hn.
    - cbn [non_null is_component]. rewrite Hn. reflexivity.
    - cbn [non_null]. rewrite Hn. reflexivity.
Qed.

(* The values of the type parameters of non-null bounds aren't nullable, as they are within their
   bounds: what a type variable made nullable in a type argument, `T?` of `T : Any`, stands for *)
Definition nonnull_values (b: Bindings): Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env x = false.

Lemma nonnull_nil: nonnull_values [].
Proof. intros p o x E. discriminate E. Qed.

Lemma yfrag_nullable_assignee: forall b A, yfrag b A -> yfrag b (nullable_assignee A).
Proof.
    intros b A HA. destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
    - exact HA.
    - exact (proj1 (yfrag_nullable b an HA)).
    - exact (yfrag_without_null b _ HA).
    - exact HA.
Qed.

Lemma variable_target_step: forall n p bnd A s r, gfrag env A = true ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing r) ->
    plus_supertype_constraint env (unify env n) s p A = Some (Ongoing r).
Proof.
    intros n p bnd A s r HA H. rewrite unify_step_once in H.
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        unfold unify_step, unify_type_variable in H; try exact H.
    - destruct (is_nullable env _); [exact H|discriminate H].
    - destruct (_ && _); [exact H|discriminate H].
    - rewrite (gfrag_intersection_not_nullable env cs HA) in H. exact H.
Qed.

Lemma variable_assignee_step: forall n p bnd A s r, gfrag env A = true ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing r) ->
    plus_subtype_constraint env (unify env n) s p A = Some (Ongoing r).
Proof.
    intros n p bnd A s r HA H. rewrite unify_step_once in H.
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]]; exact H.
Qed.

(* A type argument as the target, of a value *)
Lemma argument_takes_value: forall n v o X A s, gfrag env A = true ->
    unify env (S n) (TypeArgument v o X) A (Ongoing s) =
    if Variance_beq v output then (if is_non_nullable_nothing env A then Some (Ongoing s) else Some Failed)
    else match A with
        | Intersection cs => intersection_flipped_unify (unify env n) (TypeArgument v o X) cs s
        | _ => unify env n X A (Ongoing s)
        end.
Proof.
    intros n v o X A s HA. rewrite unify_step_once.
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]]; destruct v; reflexivity.
Qed.

(* A value as the target, of a type argument: what the type argument is read as *)
Lemma value_takes_argument: forall n A v o X s, gfrag env A = true -> (forall cs, A <> Intersection cs) ->
    unify env (S n) A (TypeArgument v o X) (Ongoing s) = unify env n A (read_type v X) (Ongoing s).
Proof.
    intros n A v o X s HA Hi. rewrite unify_step_once.
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        [reflexivity|reflexivity|reflexivity|exfalso; exact (Hi cs eq_refl)].
Qed.

Lemma component_of_fragment: forall cs c, of_fragment (Intersection cs) -> In c cs ->
    of_fragment c /\ is_component env c = true.
Proof.
    intros cs c [H Hr] Hc. destruct (intersection_gfrag env cs H) as [_ Hcs]. destruct (Hcs c Hc) as [Hcomp Hgc].
    split; [split; [exact Hgc|exact I]|exact Hcomp].
Qed.

Lemma component_no_intersection: forall c, is_component env c = true -> forall cs, c <> Intersection cs.
Proof. intros [| | | | | |] H cs E; try discriminate H; discriminate E. Qed.

(* What is below a type, non-null, is below it without null *)
Lemma below_without_null_of: forall A w, of_fragment A -> is_nullable env A = false -> of_fragment w -> below A w ->
    of_fragment (without_null env w) /\ below A (without_null env w) /\ is_nullable env (without_null env w) = false.
Proof.
    intros A w HA HnA Hw [f Hf]. split; [exact (conj (gfrag_without_null env w (proj1 Hw)) I)|].
    split; [exact (below_without_null env wf declared declared_wf f w A (proj1 Hw) (proj1 HA) HnA Hf)|].
    exact (without_null_not_nullable env wf declared declared_wf w (proj1 Hw)).
Qed.

(* ... and of a mutability no more than its own that it is assigned as no less than *)
Lemma below_given: forall A w m, of_fragment A -> of_fragment w -> below A w ->
    is_subtype_of (assignment_mutability env A) m = true -> is_subtype_of m (mutability_of env w) = true ->
    below A (with_mutability env m w).
Proof.
    intros A w m HA Hw [f Hf] HAm Hmw.
    assert (E: intersect_mutability (mutability_of env w) m = m) by (destruct m, (mutability_of env w); first [reflexivity|discriminate Hmw]).
    assert (Hr: of_fragment (with_mutability env m w))
        by (split; [exact (gfrag_with_mutability env wf declared declared_wf m w (proj1 Hw))|exact I]).
    apply (gaccepts A _ HA Hr). rewrite <- E.
    exact (instance_never_fails env wf declared declared_wf f (Some m) false w A (proj1 Hw) (proj1 HA)
        (fun m' Em => ltac:(injection Em as <-; exact HAm)) (fun En => ltac:(discriminate En)) Hf).
Qed.

Lemma fold_meet_same: forall (f: EType -> Mutability) m l, l <> [] -> (forall c, In c l -> f c = m) ->
    fold_left intersect_mutability (map f l) readonly = m.
Proof.
    intros f m [|c l] Hne H; [contradiction|]. cbn [map fold_left]. rewrite (H c (or_introl eq_refl)).
    replace (intersect_mutability readonly m) with m by (destruct m; reflexivity).
    assert (Hl: forall c', In c' l -> f c' = m) by (intros c' Hc'; exact (H c' (or_intror Hc'))). clear H Hne c.
    induction l as [|c l IH]; [reflexivity|]. cbn [map fold_left]. rewrite (Hl c (or_introl eq_refl)).
    replace (intersect_mutability m m) with m by (destruct m; reflexivity). exact (IH (fun c' Hc' => Hl c' (or_intror Hc'))).
Qed.

(* A type below each of some types of the fragment, non-null, is below the intersection of them as
   ofComponents makes it: of their components, without null, of the mutability they are assigned as in
   common *)
Lemma below_of_components: forall A ys, of_fragment A -> is_nullable env A = false -> 2 <= length ys ->
    (forall y, In y ys -> of_fragment y /\ below A y) ->
    below A (of_components env (flat_map intersected_components ys))
    /\ below A (rewrap_nullable (of_components env (flat_map intersected_components ys)))
    (* of the fragment, but where the components keep their nullability: one of them a type parameter
       that may be null, the others nullable *)
    /\ ((forall y, In y ys -> is_nullable env y = true -> match y with Nullable _ => True | _ => False end) ->
        of_fragment (of_components env (flat_map intersected_components ys)))
    /\ (of_fragment (of_components env (flat_map intersected_components ys))
        \/ exists xs, of_components env (flat_map intersected_components ys) = Intersection xs).
Proof.
    intros A ys HA HnA Hl Hys.
    (* the nullable components: nullable types, or references that may be null *)
    assert (Hzn: forall z, In z (flat_map intersected_components ys) -> is_nullable env z = true ->
        ((exists w, z = Nullable w /\ non_null env w = true /\ gfrag env w = true)
         \/ exists gm nn p, z = Generic (mkGenericRef gm nn p []))
        /\ ((forall y, In y ys -> is_nullable env y = true -> match y with Nullable _ => True | _ => False end) ->
            is_nullable_type z = true)).
    { intros z Hz' Hnz. apply in_flat_map in Hz'. destruct Hz' as [y [Hy Hzy]]. destruct (Hys y Hy) as [Hfy _].
      destruct (gfrag_cases env y (proj1 Hfy)) as [[m [c [args ->]]]|[[n [-> [Hn Hgn]]]|[[gm [nn [p [vs [-> ->]]]]]|[ds ->]]]].
      - destruct Hzy as [<-|[]]. discriminate Hnz.
      - split; [|intros _; destruct n as [| | | | | |ds]; [destruct Hzy as [<-|[]]; reflexivity..|];
                 cbn [intersected_components] in Hzy; apply in_map_iff in Hzy; destruct Hzy as [d [<- _]]; reflexivity].
        left. destruct n as [m c args|n'|g|me msg|v o n'|g|ds]; try discriminate Hn.
        + destruct Hzy as [<-|[]]. exists (RootResolved m c args). split; [reflexivity|]. split; [exact Hn|exact Hgn].
        + destruct Hzy as [<-|[]]. exists (Generic g). split; [reflexivity|]. split; [exact Hn|exact Hgn].
        + cbn [intersected_components] in Hzy. apply in_map_iff in Hzy. destruct Hzy as [d [<- Hd]].
          exists d. split; [reflexivity|]. destruct (intersection_gfrag env ds Hgn) as [_ Hds]. destruct (Hds d Hd) as [Hcd Hgd].
          split; [|exact Hgd]. destruct d; try discriminate Hcd; exact Hcd.
      - destruct Hzy as [<-|[]]. split; [right; exists gm, nn, p; reflexivity|].
        intros Hno. pose proof (Hno _ Hy Hnz) as F. contradiction F.
      - cbn [intersected_components] in Hzy. destruct (intersection_gfrag env ds (proj1 Hfy)) as [_ Hds].
        destruct (Hds z Hzy) as [Hcz _]. exfalso. destruct z; try discriminate Hcz; [discriminate Hnz|].
        cbn [is_component] in Hcz. rewrite Hnz in Hcz. discriminate Hcz. }
    (* the components, without null: class types or references, below which A is *)
    assert (Hshape: forall c, of_fragment c -> is_component env c = true ->
        match without_null env c with RootResolved _ _ _ | Generic _ => True | _ => False end).
    { intros c Hc Hcc. destruct (component_cases env c Hcc (proj1 Hc)) as [[m [d [args ->]]]|[gm [nn [p [vs [-> _]]]]]]; exact I. }
    assert (Hz: forall z, In z (flat_map intersected_components ys) ->
        of_fragment (without_null env z) /\ below A (without_null env z) /\ is_nullable env (without_null env z) = false
        /\ match without_null env z with RootResolved _ _ _ | Generic _ => True | _ => False end).
    { intros z Hz. apply in_flat_map in Hz. destruct Hz as [y [Hy Hzy]]. destruct (Hys y Hy) as [Hfy Hby].
      assert (Hcomp: forall ds d, of_fragment (Intersection ds) -> below A (Intersection ds) -> In d ds ->
          of_fragment (without_null env d) /\ below A (without_null env d) /\ is_nullable env (without_null env d) = false
          /\ match without_null env d with RootResolved _ _ _ | Generic _ => True | _ => False end).
      { intros ds d Hfi Hbi Hd. destruct (component_of_fragment ds d Hfi Hd) as [Hfd Hcd].
        destruct (below_without_null_of A d HA HnA Hfd (below_trans A _ d HA Hfi Hfd Hbi (intersection_below_component ds d Hfi Hd)))
            as [Hf' [Hb' Hn']]. exact (conj Hf' (conj Hb' (conj Hn' (Hshape d Hfd Hcd)))). }
      destruct (gfrag_cases env y (proj1 Hfy)) as [[m [c [args ->]]]|[[n [-> [Hn Hgn]]]|[[gm [nn [p [vs [-> ->]]]]]|[ds ->]]]].
      - destruct Hzy as [<-|[]]. split; [exact Hfy|]. split; [exact Hby|]. split; [reflexivity|exact I].
      - destruct n as [m c args|n'|g|me msg|v o n'|g|ds]; try discriminate Hn.
        + destruct Hzy as [<-|[]]. destruct (below_without_null_of A _ HA HnA Hfy Hby) as [Hf' [Hb' Hn']].
          split; [exact Hf'|]. split; [exact Hb'|]. split; [exact Hn'|exact I].
        + destruct Hzy as [<-|[]]. destruct (below_without_null_of A _ HA HnA Hfy Hby) as [Hf' [Hb' Hn']].
          split; [exact Hf'|]. split; [exact Hb'|]. split; [exact Hn'|]. destruct g as [gm nn p vs]. exact I.
        + (* a nullable intersection: its components made nullable, without null its components *)
          cbn [intersected_components] in Hzy. apply in_map_iff in Hzy. destruct Hzy as [d [<- Hd]].
          destruct (below_without_null_of A _ HA HnA Hfy Hby) as [Hfi [Hbi _]].
          assert (Hnd: is_nullable env (Intersection ds) = false) by (apply negb_true_iff; exact Hn).
          change (without_null env (Nullable (Intersection ds))) with (without_null env (Intersection ds)) in Hfi, Hbi.
          rewrite (without_null_not_nullable_intersection env ds Hnd) in Hfi, Hbi.
          exact (Hcomp ds d Hfi Hbi Hd).
      - destruct Hzy as [<-|[]]. destruct (below_without_null_of A _ HA HnA Hfy Hby) as [Hf' [Hb' Hn']].
        split; [exact Hf'|]. split; [exact Hb'|]. split; [exact Hn'|exact I].
      - cbn [intersected_components] in Hzy. exact (Hcomp ds z Hfy Hby Hzy). }
    assert (Hlen: 2 <= length (flat_map intersected_components ys)).
    { enough (Hge: length ys <= length (flat_map intersected_components ys)) by lia.
      assert (Hne: forall y, In y ys -> intersected_components y <> []).
      { intros y Hy. destruct (Hys y Hy) as [[Hgy _] _].
        destruct (gfrag_cases env y Hgy) as [[m [c [args ->]]]|[[n [-> [Hn Hgn]]]|[[gm [nn [p [vs [-> _]]]]]|[ds ->]]]];
            try discriminate.
        - destruct n as [m c args|n'|g|me msg|v o n'|g|ds]; try discriminate.
          destruct (intersection_gfrag env ds Hgn) as [Hds _]. cbn [intersected_components]. destruct ds; [contradiction|discriminate].
        - destruct (intersection_gfrag env ds Hgy) as [Hds _]. exact Hds. }
      clear -Hne. induction ys as [|y ys IH]; [simpl; lia|]. cbn [flat_map]. rewrite length_app. cbn [length].
      pose proof (Hne y (or_introl eq_refl)) as Hy. destruct (intersected_components y); [contradiction|].
      cbn [length]. pose proof (IH (fun y' Hy' => Hne y' (or_intror Hy'))). lia. }
    remember (flat_map intersected_components ys) as zs eqn:Ezs. clear Ezs Hys Hl.
    set (m := fold_left intersect_mutability (map (assignment_mutability env) zs) readonly).
    (* A is assigned as no more than the common mutability *)
    assert (HAm: is_subtype_of (assignment_mutability env A) m = true).
    { apply fold_intersect_greatest; [apply mutability_subtype_of_readonly|]. intros k Hk.
      apply in_map_iff in Hk. destruct Hk as [z [<- Hz']]. destruct (Hz z Hz') as [Hfz [[f Hf] _]].
      rewrite <- (assignment_mutability_without_null env wf z).
      exact (accepted_mutability env wf declared declared_wf f _ A [] (proj1 Hfz) (proj1 HA) Hf). }
    (* each component of that mutability: of the fragment, assigned as it, and A below it *)
    assert (Hw: forall z, In z zs -> of_fragment (with_mutability env m (without_null env z))
        /\ is_component env (with_mutability env m (without_null env z)) = true
        /\ assignment_mutability env (with_mutability env m (without_null env z)) = m
        /\ below A (with_mutability env m (without_null env z))).
    { intros z Hz'. destruct (Hz z Hz') as [Hfz [Hbz [Hnz Hsz]]].
      assert (Hmz: is_subtype_of m (assignment_mutability env (without_null env z)) = true).
      { rewrite (assignment_mutability_without_null env wf z).
        apply fold_intersect_below_element, in_map, Hz'. }
      split; [exact (conj (gfrag_with_mutability env wf declared declared_wf m _ (proj1 Hfz)) I)|].
      split.
      - pose proof (is_nullable_with_mutability env wf m (without_null env z)) as E2. rewrite Hnz in E2.
        revert Hsz E2. destruct (without_null env z) as [mc d args| |[gm nn p vs]| | | |]; intros Hsz E2; try contradiction; [reflexivity|].
        cbn [with_mutability] in E2 |- *. cbn [is_component]. rewrite E2. reflexivity.
      - split.
        + rewrite (assignment_with_mutability env wf declared declared_wf m _ (proj1 Hfz)).
          destruct (top_const env (without_null env z)) eqn:Et; [|reflexivity].
          rewrite (top_const_assigned_exclusive env ranked _ Et) in Hmz. exact (eq_sym (mutability_subtype_of_exclusive m Hmz)).
        + apply (below_given A _ m HA Hfz Hbz HAm).
          exact (mutability_subtype_trans _ _ _ Hmz (assignment_mutability_below env ranked _)). }
    (* a nullable component of that mutability, too *)
    assert (Hdep: forall z, In z zs -> is_nullable env z = true -> below A (with_mutability env m z)).
    { intros z Hz' Hnz. destruct (Hw z Hz') as [_ [_ [_ Hbw]]].
      destruct (proj1 (Hzn z Hz' Hnz)) as [[w [-> [Hnw Hgw]]]|[gm [nn [p ->]]]].
      - change (without_null env (Nullable w)) with (without_null env w) in Hbw.
        rewrite (without_null_unchanged env w (non_null_not_nullable env w Hnw)) in Hbw. destruct Hbw as [f Hf]. exists (S f).
        assert (Er: with_mutability env m (Nullable w) = Nullable (with_mutability env m w))
            by (destruct w as [| |[]| | | |]; first [discriminate Hnw|reflexivity]).
        rewrite Er, (nullable_target f _ A [] (proj1 HA)).
        destruct (gfrag_cases env A (proj1 HA)) as [[? [? [? ->]]]|[[? [-> _]]|[[gm' [nn' [p' [vs' [-> _]]]]]|[? ->]]]];
            [exact Hf|discriminate HnA| |exact Hf].
        cbn [nullable_assignee without_null]. change (ref_nullable env (mkGenericRef gm' nn' p' vs') = false) in HnA.
        rewrite HnA, orb_false_r. exact Hf.
      - destruct Hbw as [f Hf]. exists f. cbn [with_mutability without_null] in Hf |- *.
        assert (Hmut: forall x y, assignment_mutability env (Generic (mkGenericRef (Some m) x p []))
            = assignment_mutability env (Generic (mkGenericRef (Some m) y p []))).
        { intros x y. rewrite !(assignment_mutability_generic env ranked), !(effective_bound_adjusted env ranked).
          cbn [variables_of with_type_variables]. unfold adjusted_bound. cbn [given_mutability is_narrowed param_of].
          destruct x, y; rewrite ?(without_null_keeps_assignment_mutability env ranked); reflexivity. }
        rewrite (generic_target_bound_irrelevant env wf declared declared_wf f (Some m) nn (nn || ref_nullable env (mkGenericRef gm nn p [])) p [] A []
            (Hmut _ _) (proj1 HA) HnA).
        exact Hf. }
    set (ws := map (fun c => with_mutability env m (without_null env c)) zs).
    assert (Hws: forall w, In w ws -> of_fragment w /\ is_component env w = true /\ assignment_mutability env w = m /\ below A w).
    { intros w Hw'. unfold ws in Hw'. apply in_map_iff in Hw'. destruct Hw' as [z [<- Hz']]. exact (Hw z Hz'). }
    assert (Hfw: of_fragment (Intersection ws)).
    { split; [|exact I].
      assert (Hne: ws <> []) by (unfold ws; destruct zs; [simpl in Hlen; lia|discriminate]).
      assert (Ehm: assignment_mutability env (Intersection ws) = m).
      { cbn [assignment_mutability]. apply fold_meet_same; [exact Hne|]. intros w Hw'. exact (proj1 (proj2 (proj2 (Hws w Hw')))). }
      change (negb (Nat.eqb (length ws) 0) && forallb (fun c => is_component env c && gfrag env c) ws
          && forallb (fun c => Mutability_beq (assignment_mutability env c) (assignment_mutability env (Intersection ws))) ws = true).
      rewrite Ehm. apply andb_true_iff. split; [apply andb_true_iff; split|].
      - destruct ws; [contradiction|reflexivity].
      - apply forallb_forall. intros w Hw'. destruct (Hws w Hw') as [[Hgw _] [Hcw _]]. rewrite Hcw, Hgw. reflexivity.
      - apply forallb_forall. intros w Hw'. rewrite (proj1 (proj2 (proj2 (Hws w Hw')))). apply internal_Mutability_dec_lb. reflexivity. }
    assert (Hi: below A (Intersection ws)).
    { apply (below_intersection_of A ws HA Hfw HnA). intros w Hw'. exact (proj2 (proj2 (proj2 (Hws w Hw')))). }
    (* below an intersection, below it made nullable *)
    assert (Hrw: forall xs, below A (Intersection xs) -> below A (Nullable (Intersection xs))).
    { intros xs [f Hf]. exists (S f). rewrite (nullable_target f _ A [] (proj1 HA)).
      destruct (gfrag_cases env A (proj1 HA)) as [[? [? [? ->]]]|[[? [-> _]]|[[gm [nn [p [vs [-> _]]]]]|[? ->]]]];
          [exact Hf|discriminate HnA| |exact Hf].
      cbn [nullable_assignee without_null]. change (ref_nullable env (mkGenericRef gm nn p vs) = false) in HnA.
      rewrite HnA, orb_false_r. exact Hf. }
    unfold of_components. destruct zs as [|z1 [|z2 zs']]; [simpl in Hlen; lia|simpl in Hlen; lia|]. fold m. fold ws.
    destruct (negb (forallb (is_nullable env) (z1 :: z2 :: zs'))) eqn:Enn.
    { split; [exact Hi|]. split; [exact (Hrw ws Hi)|]. split; [intros _; exact Hfw|left; exact Hfw]. }
    assert (Hall: forall z, In z (z1 :: z2 :: zs') -> is_nullable env z = true)
        by (apply negb_false_iff in Enn; rewrite forallb_forall in Enn; exact Enn).
    destruct (forallb is_nullable_type (z1 :: z2 :: zs')) eqn:Ewr.
    { assert (Hfn: of_fragment (Nullable (Intersection ws))).
      { split; [|exact I].
        change (non_null env (Intersection ws) && gfrag env (Intersection ws) = true). rewrite (proj1 Hfw), andb_true_r.
        apply negb_true_iff. exact (gfrag_intersection_not_nullable env ws (proj1 Hfw)). }
      split; [exact (Hrw ws Hi)|]. split; [exact (Hrw ws Hi)|]. split; [intros _; exact Hfn|left; exact Hfn]. }
    (* the components keep their nullability: each takes A *)
    assert (Hdi: below A (Intersection (map (with_mutability env m) (z1 :: z2 :: zs')))).
    { destruct (uniform_fuel_list (map (with_mutability env m) (z1 :: z2 :: zs'))
          (fun f c => unify env f c A (Ongoing []) = Some (Ongoing []))) as [f Hf].
      { intros f f' c Hle E. apply (unify_fuel_monotone env f); [exact Hle|exact E]. }
      { intros c Hc. apply in_map_iff in Hc. destruct Hc as [z [<- Hz']]. exact (Hdep z Hz' (Hall z Hz')). }
      exists (S f). apply (intersection_target_takes env f _ A []).
      - intros c Hc. apply in_map_iff in Hc. destruct Hc as [z [<- Hz']].
        destruct (proj1 (Hzn z Hz' (Hall z Hz'))) as [[w [-> _]]|[gm [nn [p ->]]]];
            [cbn [with_mutability]; destruct (with_mutability env m w)|]; reflexivity.
      - discriminate.
      - destruct (gfrag_cases env A (proj1 HA)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
            first [exact I|discriminate HnA].
      - exact Hf. }
    split; [exact Hdi|]. split; [exact (Hrw _ Hdi)|]. split; [|right; eexists; reflexivity]. intros Hno. exfalso.
    assert (Ewr': forallb is_nullable_type (z1 :: z2 :: zs') = true).
    { apply forallb_forall. intros z Hz'. exact (proj2 (Hzn z Hz' (Hall z Hz')) Hno). }
    rewrite Ewr' in Ewr. discriminate Ewr.
Qed.

(* What a type argument takes, other than Nothing, is assignable to its type *)
Lemma argument_value_below: forall n v o X A, Variance_beq v output = false -> of_fragment X -> of_fragment A ->
    unify env (S n) (TypeArgument v o X) A (Ongoing []) = Some (Ongoing []) -> below A X.
Proof.
    intros n v o X A Hv HX HA H. rewrite (argument_takes_value n v o X A [] (proj1 HA)), Hv in H.
    destruct (gfrag_cases env A (proj1 HA)) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        try (exists n; exact H).
    destruct (flipped_some env n _ cs [] [] H) as [c [Hc Ec]].
    destruct (component_of_fragment cs c HA Hc) as [Hfc Hcomp].
    apply (below_trans _ c X HA Hfc HX (intersection_below_component cs c HA Hc)).
    destruct n as [|n]; [discriminate Ec|]. rewrite (argument_takes_value n v o X c [] (proj1 Hfc)), Hv in Ec.
    destruct (component_cases env c Hcomp (proj1 Hfc)) as [[mc [dc [cargs ->]]]|[gm [nn [q [bq [-> _]]]]]]; exists n; exact Ec.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Variable states                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* The bounds of the variables not bound exactly are of Qb; their static upper bounds have no type
   variables *)
Definition qstates (s: VariableStates): Prop :=
    forall p st, lookup_state s p = Some st -> is_exact st = false ->
        Qb (upper_bound st) /\ Qb (lower_bound st) /\ no_vars (static_upper_bound st) = true.

Definition gwf_states (s: VariableStates): Prop := wf_states env of_fragment of_fragment s /\ qstates s.

Lemma qstates_set: forall s p st, qstates s ->
    (is_exact st = false -> Qb (upper_bound st) /\ Qb (lower_bound st) /\ no_vars (static_upper_bound st) = true) ->
    qstates (set_state s p st).
Proof.
    intros s p st Hs Hst q st' Hq He. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. exact (Hst He).
    - rewrite lookup_set_other in Hq by exact Hne. exact (Hs q st' Hq He).
Qed.

(* A type the variable is replaced with, within what the state of the variable allows, as
   Constraints.fits: the types the type argument it is bound to exactly stands for, or the types
   between its bounds *)
Definition gfits (st: VariableState) (o: Ownership) (x: EType): Prop :=
    if is_exact st then
        exists vb ob X K, upper_bound st = TypeArgument vb ob X /\ lower_bound st = TypeArgument vb ob X
            /\ of_fragment X /\ of_fragment x
            /\ unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing []) = Some (Ongoing [])
    else below (lower_bound st) x /\ below x (upper_bound st).

Definition gsatisfies (b: Bindings) (s: VariableStates): Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        of_fragment x /\ exists st, lookup_state s p = Some st /\ gfits st o x.

Lemma gsatisfies_set_state: forall s p st st', lookup_state s p = Some st ->
    (forall o x, of_fragment x -> gfits st' o x -> gfits st o x) ->
    forall b, gsatisfies b (set_state s p st') -> gsatisfies b s.
Proof.
    intros s p st st' Hl Hf b Hb q o x Hq. destruct (Hb q o x Hq) as [Hx [st'' [Hq' Hfit]]]. split; [exact Hx|].
    destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq'. injection Hq' as <-. exists st. split; [exact Hl|exact (Hf o x Hx Hfit)].
    - rewrite lookup_set_other in Hq' by exact Hne. exists st''. auto.
Qed.

(* Whatever can be assigned to the type argument a variable is bound to can be assigned to each of
   the types it stands for *)
Lemma gwrite_leaf: forall n vb ob X o x A s u K, of_fragment X -> of_fragment x -> of_fragment A -> bottom_only A = true ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing []) = Some (Ongoing []) ->
    unify env n (TypeArgument vb ob X) A (Ongoing s) = Some (Ongoing u) ->
    u = s /\ below A x.
Proof.
    intros n vb ob X o x A s u K HX Hx HA HbA Hc H.
    destruct (keeps_free env wf n (TypeArgument vb ob X) A s u (of_fragment_no_vars X HX) (of_fragment_no_vars A HA) H) as [-> H0].
    split; [reflexivity|]. clear H.
    rewrite (unify_type_arguments env K vb ob X Model.invariant o x [] (gfrag_not_variable env X (proj1 HX))) in Hc.
    destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
    destruct n as [|n]; [discriminate H0|]. unfold compare_variances in Hc.
    destruct vb.
    - (* invariant: x is X *)
      apply (both_ways (unify env K) X x []) in Hc;
          [|apply unify_keeps_failure|intros w E; exact (gkeeps env wf K X x [] w (proj1 HX) (proj1 Hx) E)].
      exact (below_trans A X x HA HX Hx (argument_value_below n Model.invariant ob X A eq_refl HX HA H0) (ex_intro _ K (proj2 Hc))).
    - (* in: x is above X *)
      exact (below_trans A X x HA HX Hx (argument_value_below n input ob X A eq_refl HX HA H0) (ex_intro _ K Hc)).
    - (* out: nothing but Nothing, which is the bottom type *)
      rewrite (argument_takes_value n output ob X A [] (proj1 HA)) in H0. cbn [Variance_beq] in H0.
      destruct (is_non_nullable_nothing env A) eqn:En; [|discriminate H0].
      rewrite (bottom_only_nothing A (proj1 HA) HbA En). exact (below_bottom x Hx).
Qed.

(* Whatever the type argument a variable is bound to can be assigned to, each of the types it stands
   for can be assigned to *)
Lemma gread_leaf: forall n vb ob X o x A s u K, of_fragment X -> of_fragment x -> of_fragment A ->
    unify env (S K) (TypeArgument vb ob X) (TypeArgument Model.invariant o x) (Ongoing []) = Some (Ongoing []) ->
    unify env n A (TypeArgument vb ob X) (Ongoing s) = Some (Ongoing u) ->
    u = s /\ below x A.
Proof.
    intros n vb ob X o x A s u K HX Hx HA Hc H.
    destruct (keeps_free env wf n A (TypeArgument vb ob X) s u (of_fragment_no_vars A HA) (of_fragment_no_vars X HX) H) as [-> H0].
    split; [reflexivity|]. clear H.
    assert (Hr: below x (read_type vb X) /\ of_fragment (read_type vb X)).
    { rewrite (unify_type_arguments env K vb ob X Model.invariant o x [] (gfrag_not_variable env X (proj1 HX))) in Hc.
      destruct (ownership_is_assignable_to o ob); [|discriminate Hc].
      destruct vb; unfold compare_variances in Hc; cbn [read_type].
      - apply (both_ways (unify env K) X x []) in Hc;
            [|apply unify_keeps_failure|intros w E; exact (gkeeps env wf K X x [] w (proj1 HX) (proj1 Hx) E)].
        split; [exists K; exact (proj1 Hc)|exact HX].
      - split; [exact (below_top x Hx)|exact top_of_fragment].
      - split; [exists K; exact Hc|exact HX]. }
    destruct Hr as [Hxr Hfr].
    assert (Hval: forall c n', of_fragment c -> (forall cs, c <> Intersection cs) ->
        unify env n' c (TypeArgument vb ob X) (Ongoing []) = Some (Ongoing []) -> below x c).
    { intros c [|n'] Hfc Hci E; [discriminate E|].
      rewrite (value_takes_argument n' c vb ob X [] (proj1 Hfc) Hci) in E.
      exact (below_trans x _ c Hx Hfr Hfc Hxr (ex_intro _ n' E)). }
    destruct (gfrag_cases env A (proj1 HA)) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]];
        try (apply (Hval _ n HA); [intros cs E; discriminate E|exact H0]).
    destruct n as [|n]; [discriminate H0|].
    assert (Hall: forall c, In c cs -> below x c).
    { intros c Hin. destruct (component_of_fragment cs c HA Hin) as [Hfc Hcomp].
      apply (Hval c n Hfc (component_no_intersection c Hcomp)).
      exact (inter_target_all env wf n cs (TypeArgument vb ob X) [] [] (gfrag_components_no_vars env cs (proj1 HA)) (of_fragment_no_vars X HX) I H0 c Hin). }
    destruct (intersection_gfrag env cs (proj1 HA)) as [Hne _].
    destruct cs as [|c0 cs0]; [contradiction Hne; reflexivity|].
    apply (below_intersection_of x _ Hx HA); [|exact Hall].
    destruct (Hall c0 (or_introl eq_refl)) as [f Ef]. destruct (component_of_fragment _ c0 HA (or_introl eq_refl)) as [Hfc Hcomp].
    exact (accepted_not_nullable env wf declared declared_wf f c0 x [] (proj1 Hfc) (proj1 Hx) (component_not_nullable env c0 Hcomp) Ef).
Qed.

(* What the variable takes: above the lower bound, which is above it *)
Lemma gtarget_leaf: forall n p bnd A s s', gwf_states s -> of_fragment A -> bottom_only A = true -> Qb A ->
    unify env (S n) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b, gsatisfies b s' -> gsatisfies b s)
    /\ (forall o x, of_fragment x -> (forall st', lookup_state s' p = Some st' -> gfits st' o x) -> below A x).
Proof.
    intros n p bnd A s s' Hs HA HbA HqA H.
    pose proof (variable_target_step n p bnd A s s' (proj1 HA) H) as H'.
    unfold plus_supertype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (proj1 Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: its binding takes A *)
      destruct (keeps_free env wf n _ A s s' Hnl (of_fragment_no_vars A HA) H') as [-> _]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hlo in H'.
      exact (proj2 (gwrite_leaf n vb ob X o x A s s K HX Hx HA HbA Hc H')).
    - (* between bounds: the lower bound becomes the closest common supertype with A *)
      cbn zeta in H'.
      destruct (He eq_refl) as [Hcap [_ [Hbu [Hbl Hok]]]]. destruct (proj2 Hs p st Hl Ee) as [Hqu [Hql Hsc]].
      pose proof Hok as Hbs. unfold static_ok in Hbs. rewrite Hsc in Hbs.
      pose proof (supertype_of_fragment _ _ Hbl HA) as Hfs.
      destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'.
      unfold plus_static_check in H'. rewrite Hsc in H'. cbn iota in H'. injection H' as <-.
      destruct (keeps_free env wf n _ _ s ns Hnu (of_fragment_no_vars _ Hfs) E) as [-> H0].
      destruct (below_supertype _ _ Hbl HA) as [Hlo HAs].
      split; [|split].
      + split; [apply wf_set_state_closed; [exact (proj1 Hs)|intros q st' Hq E'; exact (proj2 (proj2 (proj2 Hs q st' Hq E')))
            |exact Hnu|exact (of_fragment_no_vars _ Hfs)| |exact Hsv]|].
        * intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hbu|]. split; [exact Hfs|].
          unfold static_ok. cbn [static_upper_bound upper_bound]. rewrite Hsc. exact Hbs.
        * apply qstates_set; [exact (proj2 Hs)|]. intros _. split; [exact Hqu|]. split; [exact (Qb_supertype _ _ Hbl HA Hql HqA)|exact Hsc].
      + apply (gsatisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold gfits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [E1 E2]. split; [|exact E2].
        exact (below_trans _ _ x Hbl Hfs Hx Hlo E1).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold gfits in Hfit. cbn [is_exact lower_bound] in Hfit.
        destruct Hfit as [E1 _]. exact (below_trans _ _ x HA Hfs Hx HAs E1).
Qed.

(* What the variable is assigned to: below the upper bound, which is below it *)
Lemma gassignee_leaf: forall n p bnd A s s', gwf_states s -> of_fragment A -> Qb A ->
    unify env (S n) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b, gsatisfies b s' -> gsatisfies b s)
    /\ (forall o x, of_fragment x -> (forall st', lookup_state s' p = Some st' -> gfits st' o x) -> below x A).
Proof.
    intros n p bnd A s s' Hs HA HqA H.
    pose proof (variable_assignee_step n p bnd A s s' (proj1 HA) H) as H'.
    unfold plus_subtype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
    destruct (proj1 Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: A takes what its binding gives *)
      destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars A HA) Hnu H') as [-> _]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hu in H'.
      exact (proj2 (gread_leaf n vb ob X o x A s s K HX Hx HA Hc H')).
    - (* between bounds: the upper bound becomes the intersection with A *)
      cbn zeta in H'.
      destruct (He eq_refl) as [Hcap [_ [Hbu [Hbl Hok]]]]. destruct (proj2 Hs p st Hl Ee) as [Hqu [Hql Hsc]].
      pose proof Hok as Hbs. unfold static_ok in Hbs. rewrite Hsc in Hbs.
      pose proof (intersect_of_fragment _ _ Hbu HA) as Hfi.
      destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
      destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free env wf n _ _ s ns (of_fragment_no_vars _ Hfi) Hnl E) as [-> H0].
      destruct (intersect_below_both _ _ Hbu HA) as [Hiu HiA].
      split; [|split].
      + split; [apply wf_set_state_closed; [exact (proj1 Hs)|intros q st' Hq E'; exact (proj2 (proj2 (proj2 Hs q st' Hq E')))
            |exact (of_fragment_no_vars _ Hfi)|exact Hnl| |exact Hsv]|].
        * intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hfi|]. split; [exact Hbl|].
          unfold static_ok. cbn [static_upper_bound upper_bound]. rewrite Hsc.
          intros x f Hx Ex. destruct (below_trans x _ _ Hx Hfi Hbu (ex_intro _ f Ex) Hiu) as [f1 E1]. exact (Hbs x f1 Hx E1).
        * apply qstates_set; [exact (proj2 Hs)|]. intros _. split; [exact (Qb_intersect _ _ Hbu HA Hqu HqA)|]. split; [exact Hql|exact Hsc].
      + apply (gsatisfies_set_state s p st _ Hl). intros o x Hx Hfit. unfold gfits in Hfit |- *. rewrite Ee.
        cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [E1 E2]. split; [exact E1|].
        exact (below_trans x _ _ Hx Hfi Hbu E2 Hiu).
      + intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold gfits in Hfit. cbn [is_exact upper_bound] in Hfit.
        destruct Hfit as [_ E2]. exact (below_trans x _ _ Hx Hfi HA E2 HiA).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Folds                                                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma gfold_chain: forall n (l: list (EType * EType)) s s',
    (forall t a, In (t, a) l -> forall s0 s0', gwf_states s0 -> unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
        gwf_states s0' /\ (forall b, gsatisfies b s0' -> gsatisfies b s0)) ->
    gwf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) l (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b, gsatisfies b s' -> gsatisfies b s)
    /\ (forall t a, In (t, a) l -> exists s0 s0', gwf_states s0 /\ unify env n t a (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b, gsatisfies b s' -> gsatisfies b s0')).
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

(* The parameter types of Inference.v, by their shape *)
Lemma ifrag_shapes: forall P, ifrag env P = true ->
    (exists m c args, P = RootResolved m c args)
    \/ (exists m c args, P = Nullable (RootResolved m c args) /\ ifrag env (RootResolved m c args) = true)
    \/ (exists p bnd, P = TypeVariable (mkGenericRef None false p bnd)).
Proof.
    intros P HP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> HP']]]]|[p [-> _]]]]].
    - left. eauto.
    - left. exists (Some exclusive), nothing, []. reflexivity.
    - right. left. eauto.
    - right. right. eauto.
Qed.

Section Main.

(* The types the type variables are replaced with, and the fuel with which they are within the
   bounds of the type parameters *)
Variable b: Bindings.
Variable K: nat.
Hypothesis Hnv: nonnull_values b.

Definition bindings_of_fragment: Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x.

Lemma gsatisfies_of_fragment: forall s, gsatisfies b s -> bindings_of_fragment.
Proof. intros s H p o x E. exact (proj1 (H p o x E)). Qed.

(* The types of the parameters, instantiated, are of the fragment *)
Lemma instances_of_fragment: bindings_of_fragment -> forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> args_narrowed env P = true -> bound_in env b K [] (to_generic P) = true ->
        of_fragment (inst env b P))
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> args_narrowed env a = true -> bound_in env b K [] (to_generic a) = true ->
        argument_gfrag env (instantiate env b a) = true /\ refs_wf env declared (instantiate env b a)).
Proof.
    intros Hbf. induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP _ HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (Hbf p o x Ex).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true -> args_narrowed env (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          of_fragment (inst env b (RootResolved m c args))).
      { intros m c args HP Hn HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)).
        assert (Hl: length args = length (parameter_ids env c)).
        { destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          - injection Heq as <- <- <-. exact Hl.
          - unfold bottom_type in Heq. injection Heq as _ -> ->. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
        assert (Hargs: forall a, In a args -> argument_gfrag env (instantiate env b a) = true /\ refs_wf env declared (instantiate env b a)).
        { intros a Ha. destruct (root_parts env wf b K [] m c args HP HbP a Ha) as [Hfa Hba].
          pose proof (vsize_below m c args a Ha). apply IHa; [lia|exact Hfa|exact (args_narrowed_root env m c args Hn a Ha)|exact Hba]. }
        split.
        - apply make_root_gfrag; [rewrite length_map; exact Hl|].
          intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. exact (proj1 (Hargs a Ha)).
        - exact I. }
      split.
      + intros P Hd HP Hn HbP. destruct (ifrag_shapes P HP) as [[m [c [args ->]]]|[[m [c [args [-> HP']]]]|[p [bnd ->]]]].
        * exact (Hroot m c args HP Hn HbP Hd).
        * assert (Hb': bound_in env b K [] (to_generic (RootResolved m c args)) = true) by exact HbP.
          simpl in Hd. destruct (Hroot m c args HP' Hn Hb' ltac:(simpl; lia)) as [Hg Hr].
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hg, Hr.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)). split; [exact Hg|exact Hr].
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (Hbf p o x Ex).
      + intros [| | | |v o n| |] Hd Ha Hna HbA; simpl in Ha; try discriminate Ha. simpl in Hd. change (nfrag env n = true) in Ha.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [_ Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn).
        destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [Eq _]]]]]; [exact (IHt n ltac:(lia) Ha' (narrowed_content env v o n Hna) Hbn)|].
        (* a reference of a mutability given to it, narrowed, or made nullable narrowed *)
        assert (Hbq: bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct Eq as [-> | ->]; exact Hbn).
        destruct (binds_ref_some env wf b K [] _ Hbq) as [o' [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (inst_reference env b gm nn q [] _ _ _ Ex) as [Ei Ein]. pose proof (Hbf q o' x Ex) as Hx.
        destruct Eq as [-> | ->]; [rewrite Ei; exact (ref_apply_of_fragment gm nn x Hx)|].
        rewrite Ein. simpl in Hna. destruct nn.
        { assert (Hy: of_fragment (match gm with Some m => with_mutability env (intersect_mutability (mutability_of env x) m) x | None => x end)).
          { destruct gm as [m|]; [|exact Hx]. split; [|exact I]. exact (gfrag_with_mutability env wf declared declared_wf _ x (proj1 Hx)). }
          exact (of_fragment_rewrap_narrowed _ Hy). }
        (* of a non-null bound: its value isn't null *)
        apply negb_true_iff in Hna.
        exact (of_fragment_rewrap_not_nullable _ (ref_apply_of_fragment gm false x Hx) (ref_apply_not_nullable gm false x Hx (Hnv q o' x Ex Hna))).
Qed.

Lemma instance_of_fragment: forall P, bindings_of_fragment -> ifrag env P = true -> args_narrowed env P = true ->
    bound_in env b K [] (to_generic P) = true -> of_fragment (inst env b P).
Proof. intros P Hbf HP Hn Hb. exact (proj1 (instances_of_fragment Hbf (vsize P)) P (le_n _) HP Hn Hb). Qed.

(* A type variable of a mutability given to it, narrowed or made nullable, as the target: what the
   type it stands for takes, of that mutability and nullability *)
Lemma gnested_target: forall n gm nn q P A s s', sfrag env (Generic (mkGenericRef gm nn q [])) = true ->
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yfrag b A -> gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> gsatisfies b s' -> below A (inst env b P)).
Proof.
    intros n gm nn q P A s s' Hsf EP HA Hs H.
    assert (Hstep: forall k A0, yfrag b A0 ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> gsatisfies b s' -> below A0 (ref_apply env gm nn x))).
    { intros k A0 HA0 H0.
      assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
          by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
      destruct (unify_variable_given env wf k gm nn q A0 s s' Hsh H0) as [H1 [Hgm Hnul]].
      destruct (gtarget_leaf k q [] A0 s s' Hs (proj1 HA0) (proj1 (proj2 HA0)) (proj2 (proj2 (proj2 HA0))) H1) as [Hs' [Hext Hsound]].
      split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb.
      destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state s' q = Some st'' -> gfits st'' o x)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      exact (reference_below gm nn q A0 x (proj1 HA0) Hx Hsf Hgm (fun _ => Hnul) (Hsound o x Hx Hfits)). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (Hsnd o x Ex Hsb).
    - (* made nullable: the variable takes the argument without null *)
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (Hstep n _ (yfrag_nullable_assignee b A HA) H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb. rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)).
      destruct (Hsb q o x Ex) as [Hx _].
      exact (nullable_variable_below false A _ (proj1 (proj1 HA)) (proj1 (ref_apply_of_fragment gm nn x Hx)) (Hsnd o x Ex Hsb)).
Qed.

(* ... and as the assignee: what takes the type it stands for takes it of that mutability, without
   null, or made nullable where it takes null *)
Lemma gnested_assignee: forall n gm nn q P A s s',
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yfrag b A -> gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> gsatisfies b s' -> below (inst env b P) A).
Proof.
    intros n gm nn q P A s s' EP HA Hs H.
    assert (Hstep: forall k A0, yfrag b A0 ->
        unify env (S k) A0 (TypeVariable (mkGenericRef gm nn q [])) (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> gsatisfies b s' -> below (ref_apply env gm nn x) A0)).
    { intros k A0 HA0 H0. rewrite (assignee_plain k A0 gm nn q [] s (proj1 (proj1 HA0))) in H0.
      destruct (gassignee_leaf k q [] A0 s s' Hs (proj1 HA0) (proj2 (proj2 (proj2 HA0))) H0) as [Hs' [Hext Hsound]].
      split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb.
      destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state s' q = Some st'' -> gfits st'' o x)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      exact (assigned_below gm nn x A0 Hx (proj1 HA0) (Hsound o x Hx Hfits)). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb.
      rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (Hsnd o x Ex Hsb).
    - destruct n as [|n]; [discriminate H|].
      destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [qa [ba [-> _]]]]]|[cs ->]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        destruct (Hstep n an (proj1 (yfrag_nullable b an HA)) H) as [Hs' [Hext Hsnd]].
        split; [exact Hs'|]. split; [exact Hext|]. intros o x Ex Hsb. rewrite (proj2 (inst_reference env b gm nn q [] _ _ _ Ex)).
        exact (nullable_assigned_below an _ (proj1 (proj1 HA)) (Hsnd o x Ex Hsb)).
      + rewrite step_generic_nullable in H. discriminate H.
      + rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
Qed.

(* The type parameters of the caller in the ownership of a type argument of an argument *)
Lemma ownership_kept_flipped: forall op oa, ownership_is_assignable_to op oa = true -> ownership_free b oa ->
    ownership_bound b op = true -> ownership_is_assignable_to (instantiate_ownership b op) oa = true.
Proof.
    intros op oa H Hf Hb. destruct oa as [| | |q].
    - pose proof (instantiation_preserves_ownership_assignability b op owned H) as H'. exact H'.
    - pose proof (instantiation_preserves_ownership_assignability b op ref H) as H'. exact H'.
    - reflexivity.
    - destruct op as [| | |q']; try discriminate H. simpl in H, Hf, Hb. apply param_eqb_eq in H. subst q'.
      rewrite Hf in Hb. discriminate Hb.
Qed.

(* The components of an intersection the target, one after the other *)
Lemma gfold_components: forall (h: EType -> Unification -> option Unification) (Q: EType -> Prop) cs s s',
    (forall c, h c Failed = Some Failed) ->
    (forall c s0 s0', In c cs -> gwf_states s0 -> h c (Ongoing s0) = Some (Ongoing s0') ->
        gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ (gsatisfies b s0' -> Q c)) ->
    gwf_states s -> fold_unify (fun inner c => h c inner) cs (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> forall c, In c cs -> Q c).
Proof.
    intros h Q cs. induction cs as [|c cs IH]; intros s s' Hf Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros _ c [].
    - destruct (h c (Ongoing s)) as [[s1|]|] eqn:E; try discriminate H.
      + destruct (Hstep c s s1 (or_introl eq_refl) Hs E) as [Hs1 [Hext1 Hq1]].
        destruct (IH s1 s' Hf (fun c' s0 s0' Hc' => Hstep c' s0 s0' (or_intror Hc')) Hs1 H) as [Hs' [Hext Hall]].
        split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext, Hb'|].
        intros Hsb c' [<-|Hc']; [apply Hq1, Hext, Hsb|exact (Hall Hsb c' Hc')].
      + exfalso. clear -H Hf. induction cs as [|x cs IHc]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHc H).
Qed.

(* An intersection as the target, of a class type with type variables: each of its components takes it *)
Lemma intersection_takes: forall (Q: EType -> Prop) n cs mp cp pargs s s', forallb no_vars cs = true ->
    unify env (S n) (Intersection cs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
    (forall c s0 s0', In c cs -> gwf_states s0 -> unify env n c (RootResolved mp cp pargs) (Ongoing s0) = Some (Ongoing s0') ->
        gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ (gsatisfies b s0' -> Q c)) ->
    gwf_states s -> gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> forall c, In c cs -> Q c).
Proof.
    intros Q n cs mp cp pargs s s' Hcs H Hstep Hs.
    rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H.
    destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar]. rewrite Hvar, Hnonvar in H. cbn zeta in H.
    destruct (fold_unify (fun inner component => unify env n component (RootResolved mp cp pargs) inner) cs (Ongoing s))
        as [[s2|]|] eqn:E1; try discriminate H.
    destruct (gfold_components (fun c inner => unify env n c (RootResolved mp cp pargs) inner) Q cs s s2
        (fun c => unify_keeps_failure env n c _) Hstep Hs E1) as [Hs2 [Hext2 Hall]].
    destruct (find_first (fun component => unify env n component (RootResolved mp cp pargs) (Ongoing s2)) cs)
        as [[[cov s3]|]|] eqn:E2; try discriminate H.
    - cbn in H. injection H as <-. destruct (find_first_found _ _ _ _ E2) as [Hin E3].
      destruct (Hstep cov s2 s3 Hin Hs2 E3) as [Hs3 [Hext3 _]].
      split; [exact Hs3|]. split; [intros b' Hb'; apply Hext2, Hext3, Hb'|]. intros Hsb. apply Hall, Hext3, Hsb.
    - cbn in H. injection H as <-. split; [exact Hs2|]. split; [exact Hext2|]. exact Hall.
Qed.

(*
 * Inference is sound with the type parameters of the caller in the arguments: what unify accepts of
 * an argument for a parameter, it accepts with the type variables replaced by any types that satisfy
 * the variable states it ends with. As Constraints.constraints_with_arguments, for arguments of the
 * fragment of Generics.v rather than class types.
 *)
Lemma generic_arguments: forall n,
    (forall P A s s', ifrag env P = true -> args_narrowed env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> below A (inst env b P)))
    /\ (forall P A s s', ifrag env P = true -> args_narrowed env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> below (inst env b P) A))
    /\ (forall P A s s', argument_ifrag env P = true -> args_narrowed env P = true -> argument_yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> args_narrowed env P = true -> argument_yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    (* the type of a type argument, also a type variable of a mutability given to it, narrowed or made nullable *)
    assert (IHnt: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (inst env b P))).
    { intros P A s s' HP Hn HA Hb Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP Hsf]]]]]; [exact (IHt P A s s' HP' Hn HA Hb Hs H)|].
      destruct (gnested_target n gm nn q P A s s' Hsf EP HA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros Hsb.
      assert (Hb': bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K [] _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex. exact (H3 o x Ex Hsb). }
    assert (IHna: forall P A s s', nfrag env P = true -> args_narrowed env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below (inst env b P) A)).
    { intros P A s s' HP Hn HA Hb Hs H. destruct (nfrag_cases env P HP) as [HP'|[gm [nn [q [EP _]]]]]; [exact (IHa P A s s' HP' Hn HA Hb Hs H)|].
      destruct (gnested_assignee n gm nn q P A s s' EP HA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros Hsb.
      assert (Hb': bound_in env b K [] (Generic (mkGenericRef gm nn q [])) = true) by (destruct EP as [-> | ->]; exact Hb).
      destruct (binds_ref_some env wf b K [] _ Hb') as [o [x [Ex _]]]. cbn [param_of] in Ex. exact (H3 o x Ex Hsb). }
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', gwf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        gwf_states s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> exists f, fold_unify (fun inner '(t, a) => unify env f t a inner)
            (combine (map inst_t targs) (map inst_a aargs)) (Ongoing []) = Some (Ongoing []))).
    { intros targs aargs s s' inst_t inst_a Hp Hs H.
        destruct (gfold_chain n _ s s' (fun t a Hin s0 s0' Hs0 E => let H' := Hp t a Hin s0 s0' Hs0 E in conj (proj1 H') (proj1 (proj2 H')))
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
      intros P A s s' HP Hn HA Hb Hs H.
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true -> args_narrowed env (RootResolved mt ct targs) = true ->
          yfrag b (RootResolved ma ca aargs) -> bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> below (RootResolved ma ca aargs) (inst env b (RootResolved mt ct targs)))).
      { intros mt ct targs ma ca aargs Hft Hnt Hfa Hbt Hu.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft) ltac:(solve_bound_vars)).
        pose proof (root_parts env wf b K [] mt ct targs Hft Hbt) as Htargs.
        destruct (yfrag_root b ma ca aargs Hfa) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_yfrag b a).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne).
          exact (proj2 (supertype_arguments_yfrag b ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs)). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', gwf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> exists f, unify env f (instantiate env b t) ((fun a => a) a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Htargs t Ht) as [Hft' Hbt']. exact (IHat t a s0 s0' Hft' (args_narrowed_root env mt ct targs Hnt t Ht) (Hnorm' a Ha) Hbt' Hs0 E). }
        destruct (Hpairs targs norm s s' (instantiate env b) (fun a => a) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_shapes P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP Hn HA Hb H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          destruct (IHt _ _ s s' HP Hn (yfrag_generic b _ HA) Hb Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *.
          exists (S f). rewrite step_root_generic. exact Hf.
        * (* an intersection: through the component taken *)
          rewrite step_root_inter in H. destruct (flipped_some env n _ cs s s' H) as [c [Hc Ec]].
          destruct (yfrag_component b cs c HA Hc) as [Hyc _].
          destruct (IHt _ _ s s' HP Hn Hyc Hb Hs Ec) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
          exact (below_trans _ c _ (yfrag_of_fragment b _ HA) (yfrag_of_fragment b c Hyc)
              (instance_of_fragment _ (gsatisfies_of_fragment s' Hsb) HP Hn Hb)
              (intersection_below_component cs c (yfrag_of_fragment b _ HA) Hc) (Hsound Hsb)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        destruct (IHt _ _ s s' HP' Hn (yfrag_nullable_assignee b A HA) Hb' Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
        exists (S f). rewrite (nullable_target f _ A [] (proj1 (proj1 HA))). exact Hf.
      + (* a type variable *)
        destruct (gtarget_leaf n p bnd A s s' Hs (proj1 HA) (proj1 (proj2 HA)) (proj2 (proj2 (proj2 HA))) H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> gfits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        rewrite (inst_variable env b p bnd _ _ _ Ex). exact (Hsound o x Hx Hfits).
    - (* a type with type variables as the assignee *)
      intros P A s s' HP Hn HA Hb Hs H.
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true -> args_narrowed env (RootResolved mp cp pargs) = true ->
          yfrag b (RootResolved ma ca aargs) -> bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> below (inst env b (RootResolved mp cp pargs)) (RootResolved ma ca aargs))).
      { intros ma ca aargs mp cp pargs Hfp Hnp Hfa Hbp Hu.
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp) ltac:(solve_bound_vars)).
        pose proof (root_parts env wf b K [] mp cp pargs Hfp Hbp) as Hpargs.
        destruct (yfrag_root b ma ca aargs Hfa) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn. reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hnorm': (forall a, In a norm -> argument_ifrag env a = true /\ bound_in env b K [] (to_generic a) = true)
            /\ (if class_eqb cp ca then map (instantiate env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate env b) pargs) ca) = map (instantiate env b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          destruct (supertype_commute_variables env wf b K [] cp ca pargs Hne
              (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        (* the type arguments, normalized, have the type variables made nullable narrowed *)
        assert (Hnn: forall a, In a norm -> args_narrowed env a = true).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; exact (args_narrowed_root env mp cp pargs Hnp)|].
          rewrite (class_eqb_false _ _ Hne). intros a Ha.
          assert (Hlp: length pargs = length (parameter_ids env cp)).
          { destruct (ifrag_cases env wf _ Hfp) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
                try discriminate Heq.
            - injection Heq as <- <- <-. exact Hl.
            - unfold bottom_type in Heq. injection Heq as _ -> _. rewrite class_eqb_refl in Hcn. discriminate Hcn. }
          assert (Hny: forall y, In y pargs -> nullable_narrowed env y = true)
              by (change (forallb (nullable_narrowed env) pargs = true) in Hnp; apply forallb_forall, Hnp).
          assert (Hta: forall y, In y pargs -> is_type_argument y = true)
              by (intros y Hy; exact (proj1 (argument_ifrag_parts env y (proj1 (Hpargs y Hy))))).
          pose proof (supertype_arguments_narrowed env wf cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hta Hny a Ha) as E.
          destruct a as [|[| | | | | |]| | | | |]; try reflexivity; exact E. }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', gwf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> exists f, unify env f ((fun a => a) t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. exact (IHaa a t s0 s0' Hfa' (Hnn a Ha) (Haargs t Ht) Hba' Hs0 E). }
        destruct (Hpairs aargs norm s s' (fun a => a) (instantiate env b) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP Hn HA Hb H).
        * rewrite unify_nullable_class in H.
          destruct (IHa _ _ s s' HP Hn (proj1 (yfrag_nullable b an HA)) Hb Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          injection H as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)), step_generic_root.
          cbn [is_non_nullable_nothing assignment_mutability] in Ec |- *. rewrite Ec. reflexivity.
        * (* an intersection: each of its components takes it *)
          destruct (intersection_takes (fun c => below (inst env b (RootResolved mp cp pargs)) c) n cs mp cp pargs s s'
              (gfrag_components_no_vars env cs (proj1 (proj1 HA))) H) as [Hs' [Hext Hall]];
              [|exact Hs|].
          { intros c s0 s0' Hc Hs0 E. exact (IHa _ c s0 s0' HP Hn (proj1 (yfrag_component b cs c HA Hc)) Hb Hs0 E). }
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
          pose proof (instance_of_fragment _ (gsatisfies_of_fragment s' Hsb) HP Hn Hb) as HiP.
          apply (below_intersection_of _ cs HiP (yfrag_of_fragment b _ HA)); [|exact (Hall Hsb)].
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP) ltac:(solve_bound_vars)). reflexivity.
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * rewrite unify_class_nullable in H. discriminate H.
        * rewrite unify_nullable_nullable in H.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
          destruct (IHa _ _ s s' HP' Hn (proj1 (yfrag_nullable b an HA)) Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)) in Hf.
          rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP') ltac:(solve_bound_vars)).
          exists (S f). rewrite unify_nullable_nullable. exact Hf.
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
      + (* a type variable *)
        destruct (gassignee_leaf n p bnd A s s' Hs (proj1 HA) (proj2 (proj2 (proj2 HA))) H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> gfits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        rewrite (inst_variable env b p bnd _ _ _ Ex). exact (Hsound o x Hx Hfits).
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP Hn HA Hb Hs H; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument b va oa na HA) as [HAn Hoa]. pose proof (narrowed_content env _ _ _ Hn) as Hnn.
      destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hb) as [_ Hbn].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (not_capturable env of_fragment of_fragment s nt (proj1 Hs))) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      pose proof (ownership_kept b oa ot Ho Hoa) as Hown.
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (nfrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHnt nt na s s1 HP Hnn HAn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHna nt na s1 s' HP Hnn HAn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHnt nt na s s' HP Hnn HAn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHna nt na s s' HP Hnn HAn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHnt nt top_type s s' HP Hnn (yfrag_top b) Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHna nt bottom_type s s' HP Hnn (yfrag_bottom b) Hbn Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP Hn HA Hb Hs H; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument b va oa na HA) as [HAn Hoa]. pose proof (narrowed_content env _ _ _ Hn) as Hnn.
      destruct (bound_in_argument env b K [] vp op (to_generic np) Hb) as [Hop Hbn].
      rewrite (unify_type_arguments env n va oa na vp op np s (gfrag_not_variable env na (proj1 (proj1 HAn)))) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      pose proof (ownership_kept_flipped op oa Ho Hoa Hop) as Hown.
      assert (Hgoal: forall f, compare_variances (unify env f) va vp na (inst env b np) [] = Some (Ongoing []) ->
          unify env (S f) (TypeArgument va oa na) (instantiate env b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vp op np HP Hbn).
        rewrite (unify_type_arguments env f va oa na vp _ (inst env b np) [] (gfrag_not_variable env na (proj1 (proj1 HAn)))), Hown.
        exact E. }
      pose proof (of_fragment_no_vars na (proj1 HAn)) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHna np na s s1 HP Hnn HAn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHnt np na s1 s' HP Hnn HAn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHna np na s s' HP Hnn HAn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHnt np na s s' HP Hnn HAn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free env wf k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros _; exists (S k); apply Hgoal; unfold compare_variances; exact H0
            end ].
Qed.

(* A parameter, also of a type variable of a mutability given to it, narrowed or made nullable: what the
   instance of its type takes *)
Lemma generic_parameter: forall n P A s s', pfrag env P = true -> args_narrowed env P = true -> yfrag b A -> bound_in env b K [] (pgeneric P) = true ->
    gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (inst env b P)).
Proof.
    intros n P A s s' HP Hn HA Hb Hs H. destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsf _]]]]]|[gm [nn [p [-> [Hsf _]]]]]]].
    { rewrite (pgeneric_ifrag env wf P HP') in Hb. exact (proj1 (generic_arguments n) P A s s' HP' Hn HA Hb Hs H). }
    all: destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) Hb) as [o [x [Ex _]]]; cbn [param_of] in Ex.
    all: destruct (inst_reference env b gm nn p [] _ _ _ Ex) as [Ei Ein].
    all: assert (Hstep: forall k A0, yfrag b A0 ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn p [])) A0 (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A0 (ref_apply env gm nn x))).
    all: try (intros k A0 HA0 H0;
        assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I);
        destruct (unify_variable_given env wf k gm nn p A0 s s' Hsh H0) as [H1 [Hgm Hnul]];
        destruct (gtarget_leaf k p [] A0 s s' Hs (proj1 HA0) (proj1 (proj2 HA0)) (proj2 (proj2 (proj2 HA0))) H1) as [Hs' [Hext Hsound]];
        split; [exact Hs'|]; split; [exact Hext|]; intros Hsb;
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]];
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> gfits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit);
        exact (reference_below gm nn p A0 x (proj1 HA0) Hx Hsf Hgm (fun _ => Hnul) (Hsound o x Hx Hfits))).
    - destruct n as [|n]; [discriminate H|]. rewrite Ei. exact (Hstep n A HA H).
    - (* made nullable: the variable takes the argument without null *)
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (Hstep n _ (yfrag_nullable_assignee b A HA) H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. rewrite Ein.
      destruct (Hsb p o x Ex) as [Hx _].
      exact (nullable_variable_below false A _ (proj1 (proj1 HA)) (proj1 (ref_apply_of_fragment gm nn x Hx)) (Hsnd Hsb)).
Qed.

End Main.

(* ---------------------------------------------------------------------------------------------- *)
(* Mixed types: those of the parameters, with types of the arguments in them                       *)
(*                                                                                                *)
(* Checking a candidate for a variable against its static upper bound puts the candidate, a type  *)
(* of the arguments, in place of the variable (with_candidate): in generic code, the type unify     *)
(* takes as the target mixes type variables with the types of the caller. Instantiating the type   *)
(* variables (Subtyping.instantiate_free) leaves the types of the caller as they are.              *)
(* ---------------------------------------------------------------------------------------------- *)

Section Mixed.

(* The bindings of the type variables: plain, to types of the fragment *)
Variable b: Bindings.
Hypothesis Hpb: plain_values b.
Hypothesis Hbf: forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x.

(* A type variable in a type argument, of a mutability given to it or narrowed, or made nullable,
   narrowed or bound to types that aren't nullable *)
Definition mref (t: EType): Prop :=
    match t with
    | TypeVariable (mkGenericRef gm nn q []) => sfrag env (Generic (mkGenericRef gm nn q [])) = true
    | Nullable (TypeVariable (mkGenericRef gm nn q [])) => sfrag env (Generic (mkGenericRef gm nn q [])) = true
        /\ (nn = true \/ forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> is_nullable env x = false)
    | _ => False
    end.

Lemma mref_cases: forall t, mref t -> exists gm nn q, sfrag env (Generic (mkGenericRef gm nn q [])) = true
    /\ (t = TypeVariable (mkGenericRef gm nn q [])
        \/ ((nn = true \/ forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> is_nullable env x = false)
            /\ t = Nullable (TypeVariable (mkGenericRef gm nn q [])))).
Proof.
    intros [m c args|[| | | | |[gm nn q []]|]|g|me msg|v o n|[gm nn q []]|cs] H; cbn [mref] in H; try contradiction.
    - exists gm, nn, q. split; [exact (proj1 H)|right; split; [exact (proj2 H)|reflexivity]].
    - exists gm, nn, q. split; [exact H|left; reflexivity].
Qed.

(* Class types, nullable or not, and type variables, whose type arguments are of mixed types without
   ownerships of type parameters, or of types of the arguments *)
Fixpoint mfrag (t: EType): Prop :=
    match t with
    | RootResolved _ c arguments => length arguments = length (parameter_ids env c)
        /\ fold_right (fun a acc =>
            match a with
            | TypeArgument _ o n => (yfrag b n /\ ownership_free b o) \/ (is_parameter_ownership o = false /\ (mfrag n \/ mref n))
            | _ => False
            end /\ acc) True arguments
    | Nullable n => is_class n = true /\ mfrag n
    | TypeVariable (mkGenericRef None false _ _) => True
    | _ => False
    end.

(* The type variables a type mentions are bound in b *)
Fixpoint mbinds (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => mbinds a /\ acc) True arguments
    | Nullable n => mbinds n
    | TypeArgument _ _ n => mbinds n
    | TypeVariable (mkGenericRef _ _ p _) => exists a, lookup_binding b p = Some a
    | _ => True
    end.

Definition margument (a: EType): Prop :=
    match a with
    | TypeArgument _ o n => (yfrag b n /\ ownership_free b o) \/ (is_parameter_ownership o = false /\ (mfrag n \/ mref n))
    | _ => False
    end.

Lemma mfrag_root: forall m c args, mfrag (RootResolved m c args) ->
    length args = length (parameter_ids env c) /\ forall a, In a args -> margument a.
Proof.
    intros m c args [Hl H]. split; [exact Hl|]. clear Hl.
    induction args as [|a args IH]; intros a' Ha'; [destruct Ha'|]. destruct H as [Ha Has].
    destruct Ha' as [<-|Ha']; [exact Ha|exact (IH Has a' Ha')].
Qed.

Lemma make_mfrag_root: forall m c args, length args = length (parameter_ids env c) -> (forall a, In a args -> margument a) ->
    mfrag (RootResolved m c args).
Proof.
    intros m c args Hl H. split; [exact Hl|]. clear Hl.
    induction args as [|a args IH]; [exact I|]. split; [exact (H a (or_introl eq_refl))|].
    apply IH. intros a' Ha'. exact (H a' (or_intror Ha')).
Qed.

(* A type of the arguments mentions none of the variables *)
Lemma unmentioned: forall t, gfrag env t = true -> owners_free b t -> mentions_bound b t = false.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H Ho; cbn [gfrag owners_free] in H, Ho; try discriminate H; try reflexivity.
    - apply andb_true_iff in H. destruct H as [_ H]. cbn [mentions_bound].
      induction args as [|a args IHa]; [reflexivity|]. cbn [forallb existsb] in H |- *. destruct Ho as [Hoa Hoas].
      apply andb_true_iff in H. destruct H as [Ha Has]. rewrite (IHa Has Hoas), orb_false_r.
      destruct a as [| | | |v o n| |]; try discriminate Ha. destruct Hoa as [Hof Hon]. cbn [mentions_bound].
      rewrite (IH n Ha Hon). destruct o as [| | |q]; try reflexivity. cbn [ownership_free] in Hof. rewrite Hof. reflexivity.
    - apply andb_true_iff in H. exact (IH n (proj2 H) Ho).
    - apply andb_true_iff in H. destruct H as [H _]. apply andb_true_iff in H. destruct H as [_ H]. cbn [mentions_bound].
      induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb existsb] in H |- *. destruct Ho as [Hoc Hocs].
      apply andb_true_iff in H. destruct H as [Hc Hcs]. apply andb_true_iff in Hc.
      rewrite (IH c (proj2 Hc) Hoc). exact (IHc Hcs Hocs).
Qed.

Lemma free_yfrag: forall t, yfrag b t -> instantiate_free env b t = t.
Proof.
    intros t [[Hg _] [_ [Ho _]]]. exact (free_unmentioned env b Hpb t Hg (unmentioned t Hg Ho)).
Qed.

Lemma free_ownership_free: forall o, ownership_free b o -> instantiate_free_ownership b o = o.
Proof. intros [| | |q] H; try reflexivity. cbn [ownership_free] in H. cbn [instantiate_free_ownership]. rewrite H. reflexivity. Qed.

(* Mixed types, instantiated, are no type arguments *)
Lemma mixed_nested: forall t, mfrag t -> nests_argument (instantiate_free env b t) = false.
Proof.
    intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H; cbn [mfrag] in H; try contradiction.
    - reflexivity.
    - destruct H as [Hc _]. destruct n as [m c args| | | | | |]; try discriminate Hc. reflexivity.
    - destruct gm, nn; try contradiction. cbn [instantiate_free]. destruct (lookup_binding b p) as [a|] eqn:Ha; [|reflexivity].
      destruct (Hpb p a Ha) as [Hl [o [y [-> Hy]]]]. unfold final_argument. rewrite Hl, Hy. exact Hy.
Qed.

(* A reference in a type argument, instantiated: no type argument; of the fragment, where b binds it *)
Lemma mref_nested: forall t, mref t -> nests_argument (instantiate_free env b t) = false.
Proof.
    intros t H. destruct (mref_cases t H) as [gm [nn [q [_ [-> | [_ ->]]]]]]; cbn [instantiate_free];
        destruct (lookup_binding b q) as [a|] eqn:Ha; try reflexivity;
        destruct (Hpb q a Ha) as [Hl [o [y [-> Hy]]]]; unfold final_argument; rewrite Hl, Hy; cbn [orb].
    - exact (gfrag_not_nested env _ (proj1 (ref_apply_of_fragment gm nn y (Hbf q o y Ha)))).
    - pose proof (gfrag_not_nested env _ (proj1 (ref_apply_of_fragment gm nn y (Hbf q o y Ha)))) as Hr.
      change (nests_argument (rewrap_nullable (ref_apply env gm nn y)) = false). revert Hr.
      generalize (ref_apply env gm nn y) as r. intros r Hr.
      destruct r; cbn [rewrap_nullable nests_argument] in *; first [reflexivity|exact Hr|discriminate Hr].
Qed.

Lemma mref_of_fragment: forall t, mref t -> mbinds t -> of_fragment (instantiate_free env b t).
Proof.
    intros t H Hb'. destruct (mref_cases t H) as [gm [nn [q [_ [-> | [Hnq ->]]]]]]; cbn [mbinds] in Hb'; destruct Hb' as [a Ha];
        destruct (Hpb q a Ha) as [Hl [o [y [-> Hy]]]]; cbn [instantiate_free]; rewrite Ha; unfold final_argument; rewrite Hl, Hy; cbn [orb].
    - exact (ref_apply_of_fragment gm nn y (Hbf q o y Ha)).
    - destruct Hnq as [->|Hnq].
      2:{ (* bound to types that aren't nullable *)
          apply (of_fragment_rewrap_not_nullable _ (ref_apply_of_fragment gm nn y (Hbf q o y Ha))).
          exact (ref_apply_not_nullable gm nn y (Hbf q o y Ha) (Hnq o y Ha)). }
      apply of_fragment_rewrap_narrowed.
      destruct gm as [m|]; [|exact (Hbf q o y Ha)]. split; [|exact I].
      exact (gfrag_with_mutability env wf declared declared_wf _ y (proj1 (Hbf q o y Ha))).
Qed.

Lemma margument_nested: forall n, mfrag n \/ mref n -> nests_argument (instantiate_free env b n) = false.
Proof. intros n [H|H]; [exact (mixed_nested n H)|exact (mref_nested n H)]. Qed.

(* and of the fragment, where b binds their type variables *)
Lemma mixed_of_fragment: forall t, mfrag t -> mbinds t -> of_fragment (instantiate_free env b t).
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H Hb'; cbn [mfrag mbinds] in H, Hb'; try contradiction.
    - destruct H as [Hl H]. cbn [instantiate_free]. split; [|exact I].
      apply make_root_gfrag; [rewrite length_map; exact Hl|]. clear Hl.
      induction args as [|a args IHa]; intros a' Ha'; [destruct Ha'|]. destruct H as [Hm Has]. destruct Hb' as [Hba Hbas].
      destruct Ha' as [<-|Ha']; [|exact (IHa Has Hbas a' Ha')].
      destruct a as [| | | |v o n| |]; try contradiction. destruct Hm as [[Hy Ho]|[Ho [Hn|Hn]]].
      + rewrite (free_argument env b v o n Hpb); [|rewrite (free_yfrag n Hy); exact (gfrag_not_nested env n (proj1 (proj1 Hy)))].
        rewrite (free_yfrag n Hy). exact (proj1 (proj1 Hy)).
      + cbn [mbinds] in Hba. destruct (IH n Hn Hba) as [Hgn _]. rewrite (free_argument env b v o n Hpb (mixed_nested n Hn)). exact Hgn.
      + cbn [mbinds] in Hba. destruct (mref_of_fragment n Hn Hba) as [Hgn _]. rewrite (free_argument env b v o n Hpb (mref_nested n Hn)). exact Hgn.
    - destruct H as [Hc Hn]. destruct (IH n Hn Hb') as [Hgn _]. destruct n as [m c args| | | | | |]; try discriminate Hc.
      cbn [instantiate_free] in Hgn |- *. split; [|exact I].
      cbn [rewrap_nullable gfrag non_null is_component]. exact Hgn.
    - destruct gm, nn; try contradiction. destruct Hb' as [a Ha]. destruct (Hpb p a Ha) as [Hl [o [y [-> Hy]]]].
      cbn [instantiate_free]. rewrite Ha. unfold final_argument. rewrite Hl, Hy. cbn [orb].
      exact (Hbf p o y Ha).
Qed.

Lemma margument_of_fragment: forall n, mfrag n \/ mref n -> mbinds n -> of_fragment (instantiate_free env b n).
Proof. intros n [H|H] Hb'; [exact (mixed_of_fragment n H Hb')|exact (mref_of_fragment n H Hb')]. Qed.

(* Instantiating a type argument of a mixed type keeps its variance and whether it is loose *)
Lemma free_loose: forall a, margument a -> is_loose (instantiate_free env b a) = is_loose a.
Proof.
    intros [| | | |v o n| |] H; try contradiction. destruct H as [[Hy Ho]|[Ho Hn]].
    - rewrite (free_argument env b v o n Hpb); [|rewrite (free_yfrag n Hy); exact (gfrag_not_nested env n (proj1 (proj1 Hy)))].
      rewrite (free_ownership_free o Ho). reflexivity.
    - rewrite (free_argument env b v o n Hpb (margument_nested n Hn)).
      destruct o as [| | |q]; try reflexivity. discriminate Ho.
Qed.

Lemma free_type_argument: forall v o n, is_type_argument (instantiate_free env b (TypeArgument v o n)) = true.
Proof.
    intros v o n. cbn [instantiate_free]. destruct (instantiate_free env b n) as [| [| | | |nv no nt| |] | | |nv no nt| |];
        repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity.
Qed.

(* Class types, nullable or not, instantiated, stay so *)
Lemma free_class_shaped: forall t, class_shaped t -> nests_argument (instantiate_free env b t) = false.
Proof.
    intros t [[m [c [args ->]]]|[m [c [args ->]]]]; reflexivity.
Qed.

Section MixedTemplates.

Variable sub: Class.
Variable ys: list EType.
Hypothesis Hlength: length ys = length (parameter_ids env sub).
Hypothesis Hys: forall y, In y ys -> margument y.

Let bS := bindings_of env sub ys.
Let bL := bindings_of env sub (map (instantiate_free env b) ys).

Lemma mixed_looseness: forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> mentions_loosely_bound bL t = mentions_loosely_bound bS t)
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        mentions_loosely_bound bL r = mentions_loosely_bound bS r).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + destruct (root_template env sub m c targs Ht) as [_ Htargs]. cbn [mentions_loosely_bound].
        assert (Hall: forall a, In a targs -> mentions_loosely_bound bL a = mentions_loosely_bound bS a)
            by (intros a Ha; pose proof (argument_depth_below m c targs a Ha); apply IHa; [lia|apply Htargs, Ha]).
        clear - Hall. induction targs as [|a targs IH]; [reflexivity|]. cbn [existsb].
        rewrite (Hall a (or_introl eq_refl)), IH; [reflexivity|intros a' Ha'; apply Hall; right; exact Ha'].
      + rewrite depth_nullable in Hd. cbn [mentions_loosely_bound]. exact (IHt (RootResolved m c targs) ltac:(lia) Ht').
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate_free env b) ys) i = Some (instantiate_free env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        unfold bL, bS. rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub _ i p _ Hi Hy')).
        rewrite (mentions_parameter_template _ p bp _ (lookup_parameter env wf sub ys i p y Hi Hy)).
        exact (free_loose y (Hys y (nth_error_In _ _ Hy))).
      + simpl in Hd |- *. apply IHt; [lia|exact Hn'].
Qed.

(* Instantiating a template with ys, then the type variables, is instantiating it with ys instantiated *)
Lemma mixed_template_commutes: forall k,
    (forall t, depth t <= k -> template_type env sub t = true ->
        instantiate_free env b (instantiate env bS t) = instantiate env bL t /\ mfrag (instantiate env bS t))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true ->
        instantiate_free env b (instantiate env bS r) = instantiate env bL r /\ margument (instantiate env bS r)).
Proof.
    induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    assert (Hroot: forall m c targs, depth (RootResolved m c targs) <= S k -> template_type env sub (RootResolved m c targs) = true ->
        map (instantiate_free env b) (map (instantiate env bS) targs) = map (instantiate env bL) targs
        /\ mfrag (RootResolved m c (map (instantiate env bS) targs))).
    { intros m c targs Hd Ht. destruct (root_template env sub m c targs Ht) as [Hl Htargs].
      split.
      - rewrite map_map. apply map_ext_in. intros a Ha. pose proof (argument_depth_below m c targs a Ha).
        apply IHa; [lia|apply Htargs, Ha].
      - apply make_mfrag_root; [rewrite length_map; exact Hl|]. intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]].
        pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha]. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + destruct (Hroot m c targs Hd Ht) as [E Hm]. rewrite !instantiate_class. cbn [instantiate_free]. rewrite E.
        split; [reflexivity|exact Hm].
      + rewrite depth_nullable in Hd. destruct (Hroot m c targs ltac:(lia) Ht') as [E Hm].
        rewrite !instantiate_nullable_class. cbn [instantiate_free rewrap_nullable]. rewrite E.
        split; [reflexivity|]. split; [reflexivity|exact Hm].
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hy': nth_error (map (instantiate_free env b) ys) i = Some (instantiate_free env b y))
            by (rewrite nth_error_map, Hy; reflexivity).
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hmy.
        assert (Hta: is_type_argument y = true) by (destruct y; try contradiction; reflexivity).
        assert (Hta': is_type_argument (instantiate_free env b y) = true)
            by (destruct y as [| | | |vy oy ny| |]; try contradiction; apply free_type_argument).
        unfold bS, bL. rewrite (selects env wf sub ys p bp i y Hi Hy Hta).
        rewrite (selects env wf sub _ p bp i _ Hi Hy' Hta'). split; [reflexivity|exact Hmy].
      + simpl in Hd.
        rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        rewrite (instantiate_template_argument env bL v o n Ho (template_shape env sub n Hn')).
        rewrite (proj1 (mixed_looseness (depth n)) n (le_n _) Hn').
        destruct (IHt n ltac:(lia) Hn') as [En Hmn].
        pose proof (template_instance_shape env sub bS n Hn') as Hshape.
        assert (Hio: instantiate_free_ownership b o = o) by (destruct o; first [reflexivity|discriminate Ho]).
        destruct (mentions_loosely_bound bS n); [destruct v; cbn beta iota|].
        all: first
            [ rewrite (free_argument env b _ o _ Hpb (free_class_shaped _ Hshape)), Hio, En;
              split; [reflexivity|]; right; split; [exact Ho|left; exact Hmn]
            | rewrite (free_argument env b _ o _ Hpb); [|reflexivity]; rewrite Hio;
              split; [reflexivity|]; left; split; [exact (yfrag_bottom b)|destruct o; first [exact I|discriminate Ho]] ].
Qed.

(* The type variables of a template instantiated with ys are those of ys *)
Lemma mixed_template_binds: (forall y, In y ys -> mbinds y) -> forall k,
    (forall t, depth t <= k -> template_type env sub t = true -> mbinds (instantiate env bS t))
    /\ (forall r, argument_depth r <= k -> template_argument env sub r = true -> mbinds (instantiate env bS r)).
Proof.
    intros Hb. induction k as [|k [IHt IHa]].
    { split; intros t Hd Ht; [pose proof (template_type_depth env sub t Ht)|pose proof (template_argument_depth env sub t Ht)]; lia. }
    split.
    - intros t Hd Ht. destruct (template_type_cases env sub t Ht) as [[m [c [targs ->]]]|[m [c [targs [-> Ht']]]]].
      + destruct (root_template env sub m c targs Ht) as [_ Htargs]. rewrite instantiate_class. cbn [mbinds].
        apply fold_and_map. intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha].
      + rewrite depth_nullable in Hd. rewrite instantiate_nullable_class. cbn [mbinds].
        destruct (root_template env sub m c targs Ht') as [_ Htargs].
        apply fold_and_map. intros a Ha. pose proof (argument_depth_below m c targs a Ha). apply IHa; [lia|apply Htargs, Ha].
    - intros r Hd Hr. destruct (template_kind env sub r Hr) as [[p [bp [i [-> Hi]]]]|[v [o [n [-> [_ [Ho Hn']]]]]]].
      + destruct (nth_error_same_length _ ys i p (eq_sym Hlength) Hi) as [y Hy].
        assert (Hta: is_type_argument y = true)
            by (pose proof (Hys y (nth_error_In _ _ Hy)) as Hm; destruct y; try contradiction; reflexivity).
        unfold bS. rewrite (selects env wf sub ys p bp i y Hi Hy Hta). exact (Hb y (nth_error_In _ _ Hy)).
      + simpl in Hd. rewrite (instantiate_template_argument env bS v o n Ho (template_shape env sub n Hn')).
        pose proof (IHt n ltac:(lia) Hn') as Hn.
        destruct (mentions_loosely_bound bS n); [destruct v|]; cbn [mbinds]; first [exact Hn|exact I].
Qed.

End MixedTemplates.

(* The type arguments of a supertype, normalized from those of a mixed class type, are mixed, and
   instantiating them is normalizing the instantiated type arguments *)
Lemma mixed_supertype_arguments: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> margument y) ->
    parameterized_supertype_arguments env sub (map (instantiate_free env b) ys) super
        = map (instantiate_free env b) (parameterized_supertype_arguments env sub ys super)
    /\ forall a, In a (parameterized_supertype_arguments env sub ys super) -> margument a.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite !parameterized_supertype_arguments_eq. split.
    - rewrite map_map. apply map_ext_in. intros r Hr. symmetry.
      exact (proj1 (proj2 (mixed_template_commutes sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr))).
    - intros a Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
      exact (proj2 (proj2 (mixed_template_commutes sub ys Hl Hys (argument_depth r)) r (le_n _) (Ht r Hr))).
Qed.

Lemma mixed_supertype_binds: forall sub super ys,
    sub <> super -> sub <> nothing -> base_type_is_subtype_of env sub super = true ->
    length ys = length (parameter_ids env sub) -> (forall y, In y ys -> margument y) -> (forall y, In y ys -> mbinds y) ->
    forall a, In a (parameterized_supertype_arguments env sub ys super) -> mbinds a.
Proof.
    intros sub super ys Hne Hn Hbase Hl Hys Hb a Ha.
    destruct (wf_supertypes_are_templates env wf sub super Hne Hn Hbase) as [_ Ht].
    rewrite parameterized_supertype_arguments_eq in Ha. apply in_map_iff in Ha. destruct Ha as [r [<- Hr]].
    exact (proj2 (mixed_template_binds sub ys Hl Hys Hb (argument_depth r)) r (le_n _) (Ht r Hr)).
Qed.

Lemma mfrag_cases: forall P, mfrag P ->
    (exists m c args, P = RootResolved m c args)
    \/ (exists m c args, P = Nullable (RootResolved m c args) /\ mfrag (RootResolved m c args))
    \/ (exists p bnd, P = TypeVariable (mkGenericRef None false p bnd)).
Proof.
    intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H; cbn [mfrag] in H; try contradiction.
    - left. eauto.
    - destruct H as [Hc Hn]. destruct n as [m c args| | | | | |]; try discriminate Hc. right. left. eauto.
    - destruct gm, nn; try contradiction. right. right. eauto.
Qed.

(* A type variable bound in b, instantiated: the type it is bound to *)
Lemma free_variable: forall p bnd o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    instantiate_free env b (TypeVariable (mkGenericRef None false p bnd)) = x.
Proof.
    intros p bnd o x Ha. destruct (Hpb p _ Ha) as [Hl [o' [y [E Hy]]]]. injection E as -> ->.
    cbn [instantiate_free]. rewrite Ha. unfold final_argument. rewrite Hl, Hy. reflexivity.
Qed.

(* Of any mutability given to it and narrowed or not: the type it is bound to, of that mutability and
   without null where it is narrowed *)
Lemma free_variable_any: forall gm nn p bnd o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
    instantiate_free env b (TypeVariable (mkGenericRef gm nn p bnd)) = ref_apply env gm nn x.
Proof.
    intros gm nn p bnd o x Ha. destruct (Hpb p _ Ha) as [Hl [o' [y [E Hy]]]]. injection E as -> ->.
    cbn [instantiate_free]. rewrite Ha. unfold final_argument. rewrite Hl, Hy. reflexivity.
Qed.

(* A type argument of a type of the arguments stays as it is *)
Lemma free_closed_argument: forall v o n, yfrag b n -> ownership_free b o ->
    instantiate_free env b (TypeArgument v o n) = TypeArgument v o n.
Proof.
    intros v o n Hy Ho.
    rewrite (free_argument env b v o n Hpb); [|rewrite (free_yfrag n Hy); exact (gfrag_not_nested env n (proj1 (proj1 Hy)))].
    rewrite (free_yfrag n Hy), (free_ownership_free o Ho). reflexivity.
Qed.

Section MixedInduction.

(* The variable states inference works with: none of the variables is to capture *)
Variable W: VariableStates -> Prop.
Hypothesis HW: forall s t, W s -> capturable t s = None.

(* What unify does with a type variable, at the fuel k: as gtarget_leaf and gassignee_leaf *)
Definition mleaf (k: nat): Prop :=
    (forall p bnd A s s', W s -> yfrag b A ->
        unify env (S k) (TypeVariable (mkGenericRef None false p bnd)) A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (forall o x, of_fragment x -> (forall st', lookup_state s' p = Some st' -> gfits st' o x) -> below A x))
    /\ (forall p bnd A s s', W s -> yfrag b A ->
        unify env (S k) A (TypeVariable (mkGenericRef None false p bnd)) (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (forall o x, of_fragment x -> (forall st', lookup_state s' p = Some st' -> gfits st' o x) -> below x A)).

(* What unify does with a mixed type and a type of the arguments, at the fuel n *)
Definition mstep (n: nat): Prop :=
    (forall P A s s', mfrag P -> yfrag b A -> W s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below A (instantiate_free env b P)))
    /\ (forall P A s s', mfrag P -> yfrag b A -> W s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below (instantiate_free env b P) A))
    /\ (forall P A s s', margument P -> argument_yfrag b A -> W s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> mbinds P -> exists f, unify env f (instantiate_free env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', margument P -> argument_yfrag b A -> W s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> mbinds P -> exists f, unify env f A (instantiate_free env b P) (Ongoing []) = Some (Ongoing []))).

Lemma mfold_chain: forall n (l: list (EType * EType)) s s',
    (forall t a, In (t, a) l -> forall s0 s0', W s0 -> unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)) ->
    W s -> fold_unify (fun inner '(t, a) => unify env n t a inner) l (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (forall t a, In (t, a) l -> exists s0 s0', W s0 /\ unify env n t a (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b', gsatisfies b' s' -> gsatisfies b' s0')).
Proof.
    intros n l. induction l as [|[t a] l IH]; intros s s' Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros t a [].
    - destruct (unify env n t a (Ongoing s)) as [[s1|]|] eqn:E; [|rewrite fold_stays_failed in H; discriminate H|discriminate H].
      destruct (Hstep t a (or_introl eq_refl) s s1 Hs E) as [Hs1 Hext1].
      destruct (IH s1 s' (fun t' a' Hin => Hstep t' a' (or_intror Hin)) Hs1 H) as [Hs' [Hext Hpairs]].
      split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext, Hb'|].
      intros t' a' [E'|Hin].
      + injection E' as <- <-. exists s, s1. split; [exact Hs|]. split; [exact E|exact Hext].
      + exact (Hpairs t' a' Hin).
Qed.

Lemma mfold_components: forall (h: EType -> Unification -> option Unification) (Q: EType -> Prop) cs s s',
    (forall c, h c Failed = Some Failed) ->
    (forall c s0 s0', In c cs -> W s0 -> h c (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ (gsatisfies b s0' -> Q c)) ->
    W s -> fold_unify (fun inner c => h c inner) cs (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> forall c, In c cs -> Q c).
Proof.
    intros h Q cs. induction cs as [|c cs IH]; intros s s' Hf Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros _ c [].
    - destruct (h c (Ongoing s)) as [[s1|]|] eqn:E; try discriminate H.
      + destruct (Hstep c s s1 (or_introl eq_refl) Hs E) as [Hs1 [Hext1 Hq1]].
        destruct (IH s1 s' Hf (fun c' s0 s0' Hc' => Hstep c' s0 s0' (or_intror Hc')) Hs1 H) as [Hs' [Hext Hall]].
        split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext, Hb'|].
        intros Hsb c' [<-|Hc']; [apply Hq1, Hext, Hsb|exact (Hall Hsb c' Hc')].
      + exfalso. clear -H Hf. induction cs as [|x cs IHc]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHc H).
Qed.

Lemma mintersection_takes: forall (Q: EType -> Prop) n cs mp cp pargs s s', forallb no_vars cs = true ->
    unify env (S n) (Intersection cs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
    (forall c s0 s0', In c cs -> W s0 -> unify env n c (RootResolved mp cp pargs) (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ (gsatisfies b s0' -> Q c)) ->
    W s -> W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> forall c, In c cs -> Q c).
Proof.
    intros Q n cs mp cp pargs s s' Hcs H Hstep Hs.
    rewrite unify_step_once in H. unfold unify_step, unify_intersection, intersection_body in H.
    destruct (no_vars_filter cs Hcs) as [Hvar Hnonvar]. rewrite Hvar, Hnonvar in H. cbn zeta in H.
    destruct (fold_unify (fun inner component => unify env n component (RootResolved mp cp pargs) inner) cs (Ongoing s))
        as [[s2|]|] eqn:E1; try discriminate H.
    destruct (mfold_components (fun c inner => unify env n c (RootResolved mp cp pargs) inner) Q cs s s2
        (fun c => unify_keeps_failure env n c _) Hstep Hs E1) as [Hs2 [Hext2 Hall]].
    destruct (find_first (fun component => unify env n component (RootResolved mp cp pargs) (Ongoing s2)) cs)
        as [[[cov s3]|]|] eqn:E2; try discriminate H.
    - cbn in H. injection H as <-. destruct (find_first_found _ _ _ _ E2) as [Hin E3].
      destruct (Hstep cov s2 s3 Hin Hs2 E3) as [Hs3 [Hext3 _]].
      split; [exact Hs3|]. split; [intros b' Hb'; apply Hext2, Hext3, Hb'|]. intros Hsb. apply Hall, Hext3, Hsb.
    - cbn in H. injection H as <-. split; [exact Hs2|]. split; [exact Hext2|]. exact Hall.
Qed.

(* A type argument of a type of the arguments, as a part of a mixed type: unify takes the two as they
   are, without touching the states *)
Lemma closed_argument_step: forall n v o nt A s s', yfrag b nt -> ownership_free b o -> argument_yfrag b A -> W s ->
    unify env n (TypeArgument v o nt) A (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (gsatisfies b s' -> mbinds (TypeArgument v o nt) -> exists f, unify env f (instantiate_free env b (TypeArgument v o nt)) A (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n v o nt A s s' Hy Ho HA Hs H.
    assert (HnA: no_vars A = true).
    { destruct A as [| | | |va oa na| |]; try (destruct HA as [HA _]; discriminate HA).
      exact (of_fragment_no_vars na (proj1 (proj1 (yfrag_argument b va oa na HA)))). }
    assert (Hnt: no_vars (TypeArgument v o nt) = true) by exact (of_fragment_no_vars nt (proj1 Hy)).
    destruct (keeps_free env wf n _ A s s' Hnt HnA H) as [-> H0].
    split; [exact Hs|]. split; [auto|]. intros _ _. rewrite (free_closed_argument v o nt Hy Ho). exists n. exact H0.
Qed.

Lemma closed_argument_flipped: forall n v o nt A s s', yfrag b nt -> ownership_free b o -> argument_yfrag b A -> W s ->
    unify env n A (TypeArgument v o nt) (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (gsatisfies b s' -> mbinds (TypeArgument v o nt) -> exists f, unify env f A (instantiate_free env b (TypeArgument v o nt)) (Ongoing []) = Some (Ongoing [])).
Proof.
    intros n v o nt A s s' Hy Ho HA Hs H.
    assert (HnA: no_vars A = true).
    { destruct A as [| | | |va oa na| |]; try (destruct HA as [HA _]; discriminate HA).
      exact (of_fragment_no_vars na (proj1 (proj1 (yfrag_argument b va oa na HA)))). }
    assert (Hnt: no_vars (TypeArgument v o nt) = true) by exact (of_fragment_no_vars nt (proj1 Hy)).
    destruct (keeps_free env wf n A _ s s' HnA Hnt H) as [-> H0].
    split; [exact Hs|]. split; [auto|]. intros _ _. rewrite (free_closed_argument v o nt Hy Ho). exists n. exact H0.
Qed.

(*
 * Inference is sound for mixed types, too: what unify accepts of a type of the arguments for a mixed
 * type, it accepts with the type variables replaced by any types that satisfy the variable states it
 * ends with, where unify is sound for the type variables themselves at a lower fuel (mleaf). As
 * generic_arguments, with the types of the arguments in the mixed types as they are.
 *)
(* A type variable in a type argument, of a mutability given to it or narrowed, or made nullable
   narrowed, as the target: what the type it stands for takes, of that mutability and nullability *)
Lemma mnested_target: forall n gm nn q P A s s', (forall k, k < n -> mleaf k) -> sfrag env (Generic (mkGenericRef gm nn q [])) = true ->
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yfrag b A -> W s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below A (instantiate_free env b P)).
Proof.
    intros n gm nn q P A s s' Hleaf Hsf EP HA Hs H.
    assert (Hstep: forall k A0, k < n -> yfrag b A0 ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> below A0 (ref_apply env gm nn x))).
    { intros k A0 Hk HA0 H0.
      assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
          by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
      destruct (unify_variable_given env wf k gm nn q A0 s s' Hsh H0) as [H1 [Hgm Hnul]].
      destruct (proj1 (Hleaf k Hk) q [] A0 s s' Hs HA0 H1) as [Hs' [Hext Hsound]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb o x Ex.
      destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state s' q = Some st'' -> gfits st'' o x)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      exact (reference_below gm nn q A0 x (proj1 HA0) Hx Hsf Hgm (fun _ => Hnul) (Hsound o x Hx Hfits)). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A (Nat.lt_succ_diag_r n) HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha]. destruct (Hpb q a Ha) as [Hl [o [x [-> Hy]]]].
      rewrite (free_variable_any gm nn q [] o x Ha). exact (Hsnd Hsb o x Ha).
    - destruct n as [|n]; [discriminate H|]. rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (Hstep n _ ltac:(lia) (yfrag_nullable_assignee b A HA) H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha]. destruct (Hpb q a Ha) as [Hl [o [x [-> Hy]]]].
      change (instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn q []))))
          with (rewrap_nullable (instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])))).
      rewrite (free_variable_any gm nn q [] o x Ha). destruct (Hsb q o x Ha) as [Hx _].
      exact (nullable_variable_below false A _ (proj1 (proj1 HA)) (proj1 (ref_apply_of_fragment gm nn x Hx)) (Hsnd Hsb o x Ha)).
Qed.

(* ... and as the assignee *)
Lemma mnested_assignee: forall n gm nn q P A s s', (forall k, k < n -> mleaf k) ->
    (P = TypeVariable (mkGenericRef gm nn q []) \/ P = Nullable (TypeVariable (mkGenericRef gm nn q []))) ->
    yfrag b A -> W s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below (instantiate_free env b P) A).
Proof.
    intros n gm nn q P A s s' Hleaf EP HA Hs H.
    assert (Hstep: forall k A0, k < n -> yfrag b A0 ->
        unify env (S k) A0 (TypeVariable (mkGenericRef gm nn q [])) (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> forall o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> below (ref_apply env gm nn x) A0)).
    { intros k A0 Hk HA0 H0. rewrite (assignee_plain k A0 gm nn q [] s (proj1 (proj1 HA0))) in H0.
      destruct (proj2 (Hleaf k Hk) q [] A0 s s' Hs HA0 H0) as [Hs' [Hext Hsound]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb o x Ex.
      destruct (Hsb q o x Ex) as [Hx [st' [Hl' Hfit]]].
      assert (Hfits: forall st'', lookup_state s' q = Some st'' -> gfits st'' o x)
          by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
      exact (assigned_below gm nn x A0 Hx (proj1 HA0) (Hsound o x Hx Hfits)). }
    destruct EP as [-> | ->].
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A (Nat.lt_succ_diag_r n) HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha]. destruct (Hpb q a Ha) as [Hl [o [x [-> Hy]]]].
      rewrite (free_variable_any gm nn q [] o x Ha). exact (Hsnd Hsb o x Ha).
    - destruct n as [|n]; [discriminate H|].
      destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [qa [ba [-> _]]]]]|[cs ->]]]].
      + rewrite unify_class_nullable in H. discriminate H.
      + rewrite unify_nullable_nullable in H. destruct n as [|n]; [discriminate H|].
        destruct (Hstep n an ltac:(lia) (proj1 (yfrag_nullable b an HA)) H) as [Hs' [Hext Hsnd]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha]. destruct (Hpb q a Ha) as [Hl [o [x [-> Hy]]]].
        change (instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn q []))))
            with (rewrap_nullable (instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])))).
        rewrite (free_variable_any gm nn q [] o x Ha).
        exact (nullable_assigned_below an _ (proj1 (proj1 HA)) (Hsnd Hsb o x Ha)).
      + rewrite step_generic_nullable in H. discriminate H.
      + rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
Qed.

Lemma mixed_arguments: forall n, (forall k, k < n -> mleaf k) -> mstep n.
Proof.
    induction n as [|n IHn]; intros Hleaf.
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
    destruct (IHn (fun k Hk => Hleaf k ltac:(lia))) as [IHt [IHa [IHat IHaa]]].
    destruct (Hleaf n ltac:(lia)) as [Ht_leaf Ha_leaf].
    (* the type of a type argument, also a reference of a mutability given to it, narrowed or made nullable *)
    assert (IHmt: forall P A s s', mfrag P \/ mref P -> yfrag b A -> W s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below A (instantiate_free env b P))).
    { intros P A s s' [HP|HP] HA Hs H; [exact (IHt P A s s' HP HA Hs H)|].
      destruct (mref_cases P HP) as [gm [nn [q [Hsf EP]]]].
      exact (mnested_target n gm nn q P A s s' (fun k Hk => Hleaf k ltac:(lia)) Hsf
          ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HA Hs H). }
    assert (IHma: forall P A s s', mfrag P \/ mref P -> yfrag b A -> W s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> mbinds P -> below (instantiate_free env b P) A)).
    { intros P A s s' [HP|HP] HA Hs H; [exact (IHa P A s s' HP HA Hs H)|].
      destruct (mref_cases P HP) as [gm [nn [q [_ EP]]]].
      exact (mnested_assignee n gm nn q P A s s' (fun k Hk => Hleaf k ltac:(lia))
          ltac:(destruct EP as [E|[_ E]]; [left|right]; exact E) HA Hs H). }
    (* the pairs of type arguments of two class types *)
    assert (Hpairs: forall targs aargs s s' (inst_t inst_a: EType -> EType) (R: EType -> EType -> Prop),
        (forall t a, In (t, a) (combine targs aargs) -> forall s0 s0', W s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> R t a -> exists f, unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing []))) ->
        W s -> fold_unify (fun inner '(t, a) => unify env n t a inner) (combine targs aargs) (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> (forall t a, In (t, a) (combine targs aargs) -> R t a) ->
            exists f, fold_unify (fun inner '(t, a) => unify env f t a inner)
            (combine (map inst_t targs) (map inst_a aargs)) (Ongoing []) = Some (Ongoing []))).
    { intros targs aargs s s' inst_t inst_a R Hp Hs H.
      destruct (mfold_chain n _ s s' (fun t a Hin s0 s0' Hs0 E => let H' := Hp t a Hin s0 s0' Hs0 E in conj (proj1 H') (proj1 (proj2 H')))
          Hs H) as [Hs' [Hext Hall]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hb HR.
      destruct (uniform_fuel (combine targs aargs) (fun f '(t, a) => unify env f (inst_t t) (inst_a a) (Ongoing []) = Some (Ongoing [])))
          as [f Hf].
      - intros f f' [t a] Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E).
      - intros [t a] Hin. destruct (Hall t a Hin) as [s0 [s0' [Hs0 [E Hx]]]].
        exact (proj2 (proj2 (Hp t a Hin s0 s0' Hs0 E)) (Hx b Hb) (HR t a Hin)).
      - exists f. apply fold_from_pairs. intros x y Hin. destruct (combine_map_in inst_t inst_a _ _ x y Hin) as [t [a [Hin' [-> ->]]]].
        exact (Hf (t, a) Hin'). }
    (* a type variable bound in b, instantiated *)
    assert (Hvar: forall p bnd a s', lookup_binding b p = Some a -> gsatisfies b s' ->
        exists o x, instantiate_free env b (TypeVariable (mkGenericRef None false p bnd)) = x /\ of_fragment x
            /\ forall st', lookup_state s' p = Some st' -> gfits st' o x).
    { intros p bnd a s' Ha Hsb. destruct (Hpb p a Ha) as [Hl [o [x [-> Hx]]]].
      destruct (Hsb p o x Ha) as [Hxf [st [Hl' Hfit]]].
      exists o, x. split; [exact (free_variable p bnd o x Ha)|]. split; [exact Hxf|].
      intros st' Hl''. rewrite Hl' in Hl''. injection Hl'' as <-. exact Hfit. }
    split; [|split; [|split]].
    - (* a mixed type as the target *)
      intros P A s s' HP HA Hs H.
      assert (Hroot: forall mt ct targs ma ca aargs, mfrag (RootResolved mt ct targs) -> yfrag b (RootResolved ma ca aargs) ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> mbinds (RootResolved mt ct targs) ->
              below (RootResolved ma ca aargs) (instantiate_free env b (RootResolved mt ct targs)))).
      { intros mt ct targs ma ca aargs Hft Hfa Hu. cbn [instantiate_free].
        destruct (mfrag_root mt ct targs Hft) as [_ Htargs].
        destruct (yfrag_root b ma ca aargs Hfa) as [Hla Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env ca ct) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb ca nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _ _. exists 1.
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate_free env b) targs) targs), Hm, Hcn.
          reflexivity. }
        set (norm := if class_eqb ca ct then aargs else parameterized_supertype_arguments env ca aargs ct) in Hu.
        assert (Hnorm': forall a, In a norm -> argument_yfrag b a).
        { unfold norm. destruct (Class_eq_dec ca ct) as [<-|Hne]; [rewrite class_eqb_refl; exact Haargs|].
          rewrite (class_eqb_false _ _ Hne).
          exact (proj2 (supertype_arguments_yfrag b ca ct aargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hla Haargs)). }
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine targs norm) -> forall s0 s0', W s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> mbinds t -> exists f, unify env f (instantiate_free env b t) ((fun a => a) a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          exact (IHat t a s0 s0' (Htargs t Ht) (Hnorm' a Ha) Hs0 E). }
        destruct (Hpairs targs norm s s' (instantiate_free env b) (fun a => a) (fun t _ => mbinds t) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb.
        destruct (Hsound Hsb (fun t a Hin => fold_and_in mbinds targs Hmb t (in_combine_l _ _ _ _ Hin))) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate_free env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (mfrag_cases P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          destruct (IHt _ _ s s' HP (yfrag_generic b _ HA) Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb. destruct (Hsound Hsb Hmb) as [f Hf].
          cbn [instantiate_free] in Hf |- *. exists (S f). rewrite step_root_generic. exact Hf.
        * (* an intersection: through the component taken *)
          rewrite step_root_inter in H. destruct (flipped_some env n _ cs s s' H) as [c [Hc Ec]].
          destruct (yfrag_component b cs c HA Hc) as [Hyc _].
          destruct (IHt _ _ s s' HP Hyc Hs Ec) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb.
          exact (below_trans _ c _ (yfrag_of_fragment b _ HA) (yfrag_of_fragment b c Hyc)
              (mixed_of_fragment _ HP Hmb) (intersection_below_component cs c (yfrag_of_fragment b _ HA) Hc) (Hsound Hsb Hmb)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
        destruct (IHt _ _ s s' HP' (yfrag_nullable_assignee b A HA) Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb. destruct (Hsound Hsb Hmb) as [f Hf].
        change (instantiate_free env b (Nullable (RootResolved mt ct targs)))
            with (Nullable (instantiate_free env b (RootResolved mt ct targs))).
        exists (S f). rewrite (nullable_target f _ A [] (proj1 (proj1 HA))). exact Hf.
      + (* a type variable *)
        destruct (Ht_leaf p bnd A s s' Hs HA H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha].
        destruct (Hvar p bnd a s' Ha Hsb) as [o [x [-> [Hx Hfits]]]]. exact (Hsound o x Hx Hfits).
    - (* a mixed type as the assignee *)
      intros P A s s' HP HA Hs H.
      assert (Hroot: forall ma ca aargs mp cp pargs, mfrag (RootResolved mp cp pargs) ->
          yfrag b (RootResolved ma ca aargs) ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> mbinds (RootResolved mp cp pargs) ->
              below (instantiate_free env b (RootResolved mp cp pargs)) (RootResolved ma ca aargs))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hu. cbn [instantiate_free].
        destruct (mfrag_root mp cp pargs Hfp) as [Hlp Hpargs].
        destruct (yfrag_root b ma ca aargs Hfa) as [_ Haargs].
        rewrite unify_classes in Hu.
        destruct (base_type_is_subtype_of env cp ca) eqn:Hbase; [|discriminate Hu].
        destruct (Model.is_subtype_of _ _) eqn:Hm; [|discriminate Hu].
        destruct (class_eqb cp nothing) eqn:Hcn.
        { injection Hu as <-. split; [exact Hs|]. split; [auto|]. intros _ _. exists 1.
          rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate_free env b) pargs) pargs), Hm, Hcn.
          reflexivity. }
        set (norm := if class_eqb cp ca then pargs else parameterized_supertype_arguments env cp pargs ca) in Hu.
        assert (Hnorm': (forall a, In a norm -> margument a)
            /\ (if class_eqb cp ca then map (instantiate_free env b) pargs
                else parameterized_supertype_arguments env cp (map (instantiate_free env b) pargs) ca) = map (instantiate_free env b) norm).
        { unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne]; [rewrite class_eqb_refl; split; [exact Hpargs|reflexivity]|].
          rewrite (class_eqb_false _ _ Hne).
          destruct (mixed_supertype_arguments cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs) as [Hcomm Hnormp].
          split; [exact Hnormp|exact Hcomm]. }
        destruct Hnorm' as [Hnormp Hcomm].
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', W s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> mbinds a -> exists f, unify env f ((fun a => a) t) (instantiate_free env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          exact (IHaa a t s0 s0' (Hnormp a Ha) (Haargs t Ht) Hs0 E). }
        destruct (Hpairs aargs norm s s' (fun a => a) (instantiate_free env b) (fun _ a => mbinds a) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb.
        assert (Hnb: forall a, In a norm -> mbinds a).
        { pose proof (fold_and_in mbinds pargs Hmb) as Hpb'. unfold norm. destruct (Class_eq_dec cp ca) as [<-|Hne].
          - rewrite class_eqb_refl. exact Hpb'.
          - rewrite (class_eqb_false _ _ Hne).
            exact (mixed_supertype_binds cp ca pargs Hne (class_eqb_false_neq _ _ Hcn) Hbase Hlp Hpargs Hpb'). }
        destruct (Hsound Hsb (fun t a Hin => Hnb a (in_combine_r _ _ _ _ Hin))) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate_free env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (mfrag_cases P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA H).
        * rewrite unify_nullable_class in H.
          destruct (IHa _ _ s s' HP (proj1 (yfrag_nullable b an HA)) Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb. destruct (Hsound Hsb Hmb) as [f Hf].
          cbn [instantiate_free] in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          injection H as <-. split; [exact Hs|]. split; [auto|]. intros _ _. exists 1.
          cbn [instantiate_free]. rewrite step_generic_root.
          cbn [is_non_nullable_nothing assignment_mutability] in Ec |- *. rewrite Ec. reflexivity.
        * (* an intersection: each of its components takes it *)
          destruct (mintersection_takes (fun c => mbinds (RootResolved mp cp pargs) -> below (instantiate_free env b (RootResolved mp cp pargs)) c)
              n cs mp cp pargs s s'
              (gfrag_components_no_vars env cs (proj1 (proj1 HA))) H) as [Hs' [Hext Hall]];
              [|exact Hs|].
          { intros c s0 s0' Hc Hs0 E. exact (IHa _ c s0 s0' HP (proj1 (yfrag_component b cs c HA Hc)) Hs0 E). }
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb.
          pose proof (mixed_of_fragment _ HP Hmb) as HiP.
          apply (below_intersection_of _ cs HiP (yfrag_of_fragment b _ HA)); [|exact (fun c Hc => Hall Hsb c Hc Hmb)].
          cbn [instantiate_free]. reflexivity.
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * rewrite unify_class_nullable in H. discriminate H.
        * rewrite unify_nullable_nullable in H.
          destruct (IHa _ _ s s' HP' (proj1 (yfrag_nullable b an HA)) Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb Hmb. destruct (Hsound Hsb Hmb) as [f Hf].
          change (instantiate_free env b (Nullable (RootResolved mp cp pargs)))
              with (Nullable (instantiate_free env b (RootResolved mp cp pargs))).
          exists (S f). cbn [instantiate_free] in Hf |- *. rewrite unify_nullable_nullable. exact Hf.
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H by gfrag_hyp. discriminate H.
      + (* a type variable *)
        destruct (Ha_leaf p bnd A s s' Hs HA H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ha].
        destruct (Hvar p bnd a s' Ha Hsb) as [o [x [-> [Hx Hfits]]]]. exact (Hsound o x Hx Hfits).
    - (* a type argument of a mixed type as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA Hs H; try contradiction;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      destruct HP as [[Hyt Hot]|[Hot HP]]; [exact (closed_argument_step (S n) vt ot nt _ s s' Hyt Hot HA Hs H)|].
      destruct (yfrag_argument b va oa na HA) as [HAn Hoa].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (HW s nt Hs)) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      pose proof (margument_nested nt HP) as Hnnt.
      assert (Hgoal: mbinds nt -> forall f, compare_variances (unify env f) vt va (instantiate_free env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate_free env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros Hmb f E.
        assert (Hfi: is_type_variable (instantiate_free env b nt) = false)
            by exact (gfrag_not_variable env _ (proj1 (margument_of_fragment nt HP Hmb))).
        rewrite (free_argument env b vt ot nt Hpb Hnnt), (free_plain_ownership b ot Hot).
        rewrite (unify_type_arguments env f vt _ (instantiate_free env b nt) va oa na [] Hfi), Ho. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHmt nt na s s1 HP HAn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHma nt na s1 s' HP HAn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb Hmb.
           destruct (Hsnd2 Hsb Hmb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb) Hmb) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal Hmb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHmt nt na s s' HP HAn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHma nt na s s' HP HAn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHmt nt top_type s s' HP (yfrag_top b) Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHma nt bottom_type s s' HP (yfrag_bottom b) Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros Hsb Hmb; destruct (Hsnd Hsb Hmb) as [f Hf];
          exists (S f); apply (Hgoal Hmb); unfold compare_variances; exact Hf.
    - (* a type argument of a mixed type as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA Hs H; try contradiction;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      destruct HP as [[Hyp Hop]|[Hop HP]]; [exact (closed_argument_flipped (S n) vp op np _ s s' Hyp Hop HA Hs H)|].
      destruct (yfrag_argument b va oa na HA) as [HAn Hoa].
      rewrite (unify_type_arguments env n va oa na vp op np s (gfrag_not_variable env na (proj1 (proj1 HAn)))) in H.
      destruct (ownership_is_assignable_to op oa) eqn:Ho; [|discriminate H].
      pose proof (margument_nested np HP) as Hnnp.
      assert (Hgoal: mbinds np -> forall f, compare_variances (unify env f) va vp na (instantiate_free env b np) [] = Some (Ongoing []) ->
          unify env (S f) (TypeArgument va oa na) (instantiate_free env b (TypeArgument vp op np)) (Ongoing []) = Some (Ongoing [])).
      { intros _ f E. rewrite (free_argument env b vp op np Hpb Hnnp), (free_plain_ownership b op Hop).
        rewrite (unify_type_arguments env f va oa na vp _ (instantiate_free env b np) [] (gfrag_not_variable env na (proj1 (proj1 HAn)))), Ho.
        exact E. }
      pose proof (of_fragment_no_vars na (proj1 HAn)) as Hnna.
      destruct va, vp; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n na np (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHma np na s s1 HP HAn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHmt np na s1 s' HP HAn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb Hmb.
           destruct (Hsnd2 Hsb Hmb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb) Hmb) as [f1 Hf1].
           exists (S (max f1 f2)). apply (Hgoal Hmb). unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHma np na s s' HP HAn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb Hmb; destruct (Hsnd Hsb Hmb) as [f Hf];
            exists (S f); apply (Hgoal Hmb); unfold compare_variances; exact Hf
          | destruct (IHmt np na s s' HP HAn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb Hmb; destruct (Hsnd Hsb Hmb) as [f Hf];
            exists (S f); apply (Hgoal Hmb); unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free env wf k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros _ Hmb; exists (S k); apply (Hgoal Hmb); unfold compare_variances; exact H0
            end ].
Qed.

End MixedInduction.

End Mixed.

(* ---------------------------------------------------------------------------------------------- *)
(* Static upper bounds that are intersections                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* What a class type takes, type variables in its type arguments or not, is non-null, and assigned as
   below it *)
Lemma root_takes: forall n m cl args a s s', gfrag env a = true ->
    unify env n (RootResolved m cl args) a (Ongoing s) = Some (Ongoing s') ->
    is_nullable env a = false
    /\ Model.is_subtype_of (assignment_mutability env a) (assignment_mutability env (RootResolved m cl args)) = true.
Proof.
    induction n as [|n IH]; intros m cl args a s s' Ha H; [discriminate H|].
    destruct (gfrag_cases env a Ha) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [pa [ba [-> Hba]]]]]|[acs ->]]]].
    - split; [reflexivity|]. rewrite unify_classes in H. destruct (base_type_is_subtype_of env ca cl); [|discriminate H].
      destruct (Model.is_subtype_of _ _) eqn:E; [reflexivity|discriminate H].
    - rewrite unify_class_nullable in H. discriminate H.
    - rewrite step_root_generic in H. rewrite (is_nullable_generic env ranked), (assignment_mutability_generic env ranked).
      exact (IH m cl args _ s s' (bound_gfrag env wf declared declared_wf _ Ha) H).
    - split; [exact (gfrag_intersection_not_nullable env acs Ha)|]. rewrite step_root_inter in H. destruct (flipped_some env n _ acs s s' H) as [c [Hc Hu]].
      eapply mutability_subtype_trans; [apply (intersection_assignment_mutability_below_component env), Hc|].
      exact (proj2 (IH m cl args c s s' (proj2 (proj2 (intersection_gfrag env acs Ha) c Hc)) Hu)).
Qed.

(* The mutability given to a type variable as the target only rejects types assigned as beyond it *)
Lemma variable_mutability_given: forall k m q A s s', gfrag env A = true ->
    unify env (S k) (TypeVariable (mkGenericRef (Some m) false q [])) A (Ongoing s) = Some (Ongoing s') ->
    unify env (S k) (TypeVariable (mkGenericRef None false q [])) A (Ongoing s) = Some (Ongoing s').
Proof.
    intros k m q A s s' HA H.
    assert (Hn: is_nullable env (TypeVariable (mkGenericRef (Some m) false q []))
        = is_nullable env (TypeVariable (mkGenericRef None false q []))).
    { rewrite !(is_nullable_type_variable env ranked), !(effective_bound_eq env ranked).
      cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
      apply (is_nullable_with_mutability env wf). }
    rewrite unify_step_once in H |- *. unfold unify_step, unify_type_variable in H |- *.
    destruct (gfrag_cases env A HA) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [pa [ba [-> _]]]]]|[acs ->]]]];
        cbn beta iota in H |- *;
        match type of H with context [given_mutability_fits ?e ?x ?y] => destruct (given_mutability_fits e x y) end;
        cbn [negb] in H |- *; try discriminate H; rewrite ?Hn in H; exact H.
Qed.

(* Of a class type as the target, only the mutability it is assigned as matters *)
Lemma unify_root_mutability_any: forall k m1 m2 cl args A carry, gfrag env A = true ->
    assignment_mutability env (RootResolved m1 cl args) = assignment_mutability env (RootResolved m2 cl args) ->
    unify env k (RootResolved m1 cl args) A carry = unify env k (RootResolved m2 cl args) A carry.
Proof.
    induction k as [|k IH]; intros m1 m2 cl args A [s|] HA Hm; try reflexivity.
    destruct (gfrag_cases env A HA) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[ga [nga [pa [ba [-> _]]]]]|[acs ->]]]].
    - rewrite !unify_classes, Hm. reflexivity.
    - rewrite !unify_class_nullable. reflexivity.
    - rewrite !step_root_generic. exact (IH m1 m2 cl args _ (Ongoing s) (bound_gfrag env wf declared declared_wf _ HA) Hm).
    - rewrite !step_root_inter. unfold intersection_flipped_unify.
      assert (E: find_first (fun component => unify env k (RootResolved m1 cl args) component (Ongoing s)) acs
          = find_first (fun component => unify env k (RootResolved m2 cl args) component (Ongoing s)) acs).
      { destruct (intersection_gfrag env acs HA) as [_ Hcs]. clear HA. induction acs as [|c acs IHc]; [reflexivity|]. simpl.
        rewrite (IH m1 m2 cl args c (Ongoing s) (proj2 (Hcs c (or_introl eq_refl))) Hm).
        rewrite IHc; [reflexivity|]. intros c' Hc'. apply Hcs. right. exact Hc'. }
      rewrite E. reflexivity.
Qed.

Lemma any_of_fragment: forall m, of_fragment (RootResolved (Some m) any []).
Proof.
    intros m. split; [|exact I]. change (Nat.eqb 0 (length (parameter_ids env any)) && true = true).
    rewrite (wf_any_has_no_type_parameters env wf). reflexivity.
Qed.

(* `m Any` is above what is non-null and assigned as below m *)
Lemma below_any_of: forall m t, of_fragment t -> is_nullable env t = false ->
    Model.is_subtype_of (assignment_mutability env t) m = true -> below t (RootResolved (Some m) any []).
Proof.
    intros m t Ht Hn Hm. apply gaccepts; [exact Ht|exact (any_of_fragment m)|].
    exact (any_mutability_never_fails env wf declared declared_wf m t (proj1 Ht) Hn Hm).
Qed.

Local Notation "'let*' x ':=' e 'in' body" :=
    (match e with Some x => body | None => None end) (at level 200, x name, e at level 100, body at level 200).

Lemma unify_intersection_body: forall u self cs a s, match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end ->
    unify_intersection env u self cs a s = intersection_body env u cs a s.
Proof. intros u self cs [| | | | | |] s Ha; try contradiction; reflexivity. Qed.

(* A fold of steps that keep the variable states as W has them, each with the states it starts and
   ends with *)
Lemma gfold_list: forall (W: VariableStates -> Prop) (h: EType -> Unification -> option Unification) l s s',
    (forall x, h x Failed = Some Failed) ->
    (forall x s0 s0', In x l -> W s0 -> h x (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)) ->
    W s -> fold_unify (fun inner x => h x inner) l (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
    /\ (forall x, In x l -> exists s0 s0', W s0 /\ h x (Ongoing s0) = Some (Ongoing s0')
        /\ (forall b', gsatisfies b' s' -> gsatisfies b' s0')).
Proof.
    intros W h l. induction l as [|x l IH]; intros s s' Hf Hstep Hs H; simpl in H.
    - injection H as <-. split; [exact Hs|]. split; [auto|]. intros x [].
    - destruct (h x (Ongoing s)) as [[s1|]|] eqn:E.
      + destruct (Hstep x s s1 (or_introl eq_refl) Hs E) as [Hs1 Hext1].
        destruct (IH s1 s' Hf (fun x' s0 s0' Hx' => Hstep x' s0 s0' (or_intror Hx')) Hs1 H) as [Hs' [Hext Hall]].
        split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext, Hb'|].
        intros x' [<-|Hx']; [exists s, s1; split; [exact Hs|]; split; [exact E|exact Hext]|exact (Hall x' Hx')].
      + exfalso. clear -H Hf. induction l as [|y l IHl]; simpl in H; [discriminate H|]. rewrite Hf in H. exact (IHl H).
      + discriminate H.
Qed.

(* What a value of a static upper bound is a value of: the components of an intersection, or the bound *)
Definition bound_components (S: EType): list EType :=
    match S with Intersection cs => cs | Nullable (Intersection cs) => map Nullable cs | _ => [S] end.

Lemma vars_in_bound_component: forall P S C, vars_in P S = true -> In C (bound_components S) -> vars_in P C = true.
Proof.
    intros P [m c args|[m' c' a'|n'|g'|me' msg'|v' o' x'|g'|cs']|g|me msg|v o x|g|cs] C H HC; cbn [bound_components] in HC;
        try (destruct HC as [<-|[]]; exact H).
    - cbn [vars_in] in H. apply in_map_iff in HC. destruct HC as [c [<- Hc]]. rewrite forallb_forall in H. exact (H c Hc).
    - cbn [vars_in] in H. rewrite forallb_forall in H. exact (H C HC).
Qed.

(* Of a bound of the fragment, each such component is of it, and above the bound *)
Lemma bound_component_of: forall S C, of_fragment S -> Qb S -> In C (bound_components S) ->
    of_fragment C /\ Qb C /\ below S C.
Proof.
    intros S C HS HqS HC. destruct S as [m c args|[m' c' a'|n'|g'|me' msg'|v' o' x'|g'|cs]|g|me msg|v o x|g|cs]; cbn [bound_components] in HC;
        try (destruct HC as [<-|[]]; split; [exact HS|]; split; [exact HqS|exact (below_refl _ HS)]).
    - (* of a nullable intersection, its components made nullable *)
      apply in_map_iff in HC. destruct HC as [c [<- Hc]].
      assert (HI: of_fragment (Intersection cs)) by (split; [pose proof (proj1 HS) as HgS; cbn [gfrag] in HgS; apply andb_true_iff in HgS; exact (proj2 HgS)|exact I]).
      destruct (proj2 (intersection_gfrag env cs (proj1 HI)) c Hc) as [Hcc Hgc].
      split; [split; [|exact I]|split; [exact (Qb_nullable_component cs c HqS Hc)|]].
      + cbn [gfrag]. rewrite Hgc, andb_true_r. destruct c; first [exact Hcc|discriminate Hcc].
      + destruct (intersection_below_component cs c HI Hc) as [k Ek]. exists (S k). rewrite unify_nullable_nullable. exact Ek.
    - split; [|split; [exact (Qb_component cs C HqS HC)|exact (intersection_below_component cs C HS HC)]].
      split; [exact (proj2 (proj2 (intersection_gfrag env cs (proj1 HS)) C HC))|exact I].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Static upper bounds with type variables, in generic code                                        *)
(*                                                                                                *)
(* A variable whose declared bound mentions type variables keeps it as its static upper bound; each *)
(* lower bound is checked against it with the lower bound in place of the variable itself          *)
(* (plus_static_check). In generic code, that lower bound is a type of the arguments, of the types  *)
(* of the caller: the check unifies a mixed type (mixed_arguments). The states inference works with *)
(* here (gwf2) record that each lower bound is below its static upper bound, with the variable bound *)
(* to it and the others to whatever satisfies the states (gstatic_checked).                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section GenericStatic.

Definition bound_b (b: Bindings) (q: TypeParameterId): bool := match lookup_binding b q with Some _ => true | None => false end.

Lemma is_nullable_to_generic: forall t, is_nullable env (to_generic t) = is_nullable env t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; cbn [to_generic is_nullable]; try reflexivity.
    - exact (IH n).
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [map forallb]. rewrite (IH c), IHc. reflexivity.
Qed.

(* A bound that isn't nullable has a component that isn't *)
Lemma bound_components_not_nullable: forall S, is_nullable env S = false ->
    exists C, In C (bound_components S) /\ is_nullable env C = false.
Proof.
    intros [m c args|n|g|me msg|v o n|g|cs] H; cbn [bound_components];
        try (cbn [is_nullable] in H; discriminate H); try (eexists; split; [left; reflexivity|exact H]).
    cbn [is_nullable] in H. revert H. induction cs as [|c cs IH]; intros H; [discriminate H|].
    cbn [forallb] in H. destruct (is_nullable env c) eqn:Ec; [|exists c; split; [left; reflexivity|exact Ec]].
    destruct (IH H) as [C [HC HnC]]. exists C. split; [right; exact HC|exact HnC].
Qed.

(*
 * The values of type parameters of non-null bounds aren't nullable, where each is within its declared
 * bound S, as Kotlin checks them: below it, below each of its components, or, a bound mentioning type
 * variables, below the instance of each of its components. By the ranks of the type parameters: the
 * type variables in a bound are of a lower rank than the type parameter bounded.
 *)
Lemma values_not_nullable: forall b, plain_values b ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
    (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> exists S, to_generic S = parameter_bound env q
        /\ ((gfrag env S = true /\ below x S)
            \/ (forall C, In C (bound_components S) -> gfrag env C = true /\ below x C)
            \/ (forall C, In C (bound_components S) -> pfrag env C = true /\ vars_in (bound_b b) C = true
                /\ below x (instantiate_free env b C)))) ->
    nonnull_values b.
Proof.
    intros b Hpb Hbf Hform q. remember (parameter_rank env q) as r eqn:Er. revert q Er.
    induction r as [r IH] using lt_wf_ind. intros q -> o x Eq Hnq.
    destruct (Hform q o x Eq) as [S [ES Hcases]].
    assert (HnS: is_nullable env S = false).
    { rewrite <- is_nullable_to_generic, ES, <- (effective_bound_plain env ranked), <- (is_nullable_generic env ranked). exact Hnq. }
    pose proof (Hbf q o x Eq) as Hx.
    assert (Hacc: forall t, gfrag env t = true -> is_nullable env t = false -> below x t -> is_nullable env x = false).
    { intros t Ht Hnt [f Ef]. exact (accepted_not_nullable env wf declared declared_wf f t x [] Ht (proj1 Hx) Hnt Ef). }
    destruct (bound_components_not_nullable S HnS) as [C [HC HnC]].
    destruct Hcases as [[HgS HbS]|[Hcl|Hvar]].
    - exact (Hacc S HgS HnS HbS).
    - destruct (Hcl C HC) as [HgC HbC]. exact (Hacc C HgC HnC HbC).
    - destruct (Hvar C HC) as [HCp [HvC [f Ef]]].
      (* a component of the bound: of a lower rank *)
      assert (Hr: ranked_below env (parameter_rank env q) (to_generic C) = true).
      { pose proof (wf_bounds_ranked env wf q) as Hrk. rewrite <- ES in Hrk.
        destruct S as [m c args|[m' c' a'|n'|g''|me' msg'|v' o' x'|g''|cs]|g'|me msg|v o' x'|g'|cs]; cbn [bound_components] in HC;
            try (destruct HC as [<-|[]]; exact Hrk); cbn [to_generic ranked_below] in Hrk;
            change (forallb (ranked_below env (parameter_rank env q)) (map to_generic cs) = true) in Hrk;
            rewrite forallb_forall in Hrk.
        - apply in_map_iff in HC. destruct HC as [c [<- Hc]]. exact (Hrk _ (in_map to_generic _ _ Hc)).
        - exact (Hrk _ (in_map to_generic _ _ HC)). }
      (* a type variable: the value of a type parameter of a lower rank, or without null *)
      assert (Href: forall gm nn p, C = TypeVariable (mkGenericRef gm nn p []) -> is_nullable env x = false).
      { intros gm nn p ->. cbn [vars_in] in HvC. rewrite andb_true_r in HvC. unfold bound_b in HvC.
        destruct (lookup_binding b p) as [a|] eqn:Ea; [|discriminate HvC].
        destruct (Hpb p a Ea) as [Hla [o' [x' [-> Hy]]]].
        assert (Ei: instantiate_free env b (TypeVariable (mkGenericRef gm nn p [])) = ref_apply env gm nn x')
            by (cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hla, Hy; reflexivity).
        rewrite Ei in Ef. apply (Hacc _ (proj1 (ref_apply_of_fragment gm nn x' (Hbf p o' x' Ea))));
            [|exists f; exact Ef].
        destruct nn.
        - change (ref_apply env gm true x') with (without_null env (ref_apply env gm false x')).
          exact (Generics.without_null_not_nullable env wf declared declared_wf _
              (proj1 (ref_apply_of_fragment gm false x' (Hbf p o' x' Ea)))).
        - cbn [to_generic ranked_below] in Hr. unfold rank_of in Hr. cbn [param_of] in Hr. apply Nat.ltb_lt in Hr.
          assert (Hnp: is_nullable env (Generic (mkGenericRef None false p [])) = false).
          { destruct gm as [m|]; [|exact HnC].
            change (is_nullable env (TypeVariable (mkGenericRef (Some m) false p [])))
                with (is_nullable env (Generic (mkGenericRef (Some m) false p []))) in HnC.
            change (Generic (mkGenericRef (Some m) false p [])) with (with_mutability env m (Generic (mkGenericRef None false p []))) in HnC.
            rewrite (is_nullable_with_mutability env wf) in HnC. exact HnC. }
          pose proof (IH _ Hr p eq_refl o' x' Ea Hnp) as Hnx'.
          destruct gm as [m|]; [cbn [ref_apply]; rewrite (is_nullable_with_mutability env wf)|]; exact Hnx'. }
      destruct (pfrag_cases env C HCp) as [Hi|[[gm [nn [p [EC _]]]]|[gm [nn [p [-> _]]]]]].
      + destruct (ifrag_cases env wf C Hi) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [EC _]]]]].
        * cbn [instantiate_free] in Ef. exact (root_accepts_not_nullable env wf declared declared_wf f _ _ _ x [] (proj1 Hx) Ef).
        * unfold bottom_type in Ef. cbn [instantiate_free] in Ef.
          exact (root_accepts_not_nullable env wf declared declared_wf f _ _ _ x [] (proj1 Hx) Ef).
        * cbn [is_nullable] in HnC. discriminate HnC.
        * exact (Href None false p EC).
      + exact (Href gm nn p EC).
      + cbn [is_nullable] in HnC. discriminate HnC.
Qed.

(* A value within a declared bound that isn't nullable isn't either *)
Lemma within_bound_not_nullable: forall p S x, to_generic S = parameter_bound env p -> gfrag env S = true -> gfrag env x = true ->
    below x S -> is_nullable env (Generic (mkGenericRef None false p [])) = false -> is_nullable env x = false.
Proof.
    intros p S x ES HS Hx [f Ef] Hn.
    rewrite (is_nullable_generic env ranked), (effective_bound_plain env ranked), <- ES, is_nullable_to_generic in Hn.
    exact (accepted_not_nullable env wf declared declared_wf f S x [] HS Hx Hn Ef).
Qed.

Lemma lookup_map_pairs: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId * EType -> EType) p a,
    lookup_binding (map (fun v => (fst v, g v)) l) p = Some a -> exists v, In v l /\ fst v = p /\ a = g v.
Proof.
    induction l as [|v l IH]; intros g p a E; [discriminate E|]. cbn [map lookup_binding] in E.
    destruct (param_eqb p (fst v)) eqn:Eq.
    - apply param_eqb_eq in Eq. injection E as <-. exists v. split; [left; reflexivity|split; [symmetry; exact Eq|reflexivity]].
    - destruct (IH g p a E) as [v' [Hin [Hf Ea]]]. exists v'. split; [right; exact Hin|split; assumption].
Qed.


(* The form of a static upper bound with type variables: types of the parameters without ownerships of
   type parameters, other than the variable itself, a type variable of a mutability given to it,
   narrowed or made nullable among them (pfrag), or an intersection, nullable or not, of components of
   ifrag or type variables (compfrag), assigned as one mutability, as ofComponents makes them *)
(* No ownerships of type parameters; the type variables made nullable in type arguments narrowed, or
   of non-null bounds, and none of those in type arguments but plain ones p *)
Definition bplain (p: TypeParameterId) (t: EType): bool := plain_owners t && (args_narrowed env t && args_avoid p t).

Lemma bplain_parts: forall p t, bplain p t = true -> plain_owners t = true /\ args_narrowed env t = true /\ args_avoid p t = true.
Proof.
    intros p t H. unfold bplain in H. apply andb_true_iff in H. destruct H as [H1 H]. apply andb_true_iff in H. exact (conj H1 H).
Qed.

Lemma bplain_nullable: forall p C, bplain p (Nullable C) = true -> bplain p C = true.
Proof.
    intros p C H. destruct (bplain_parts p _ H) as [Ho [Hn Ha]].
    cbn [plain_owners args_avoid] in Ho, Ha.
    unfold bplain. rewrite Ho, Ha, andb_true_r. cbn [andb].
    destruct C as [m c args|[m c args|n|[gm nn q vs]|me msg|v o n|[gm nn q vs]|cs]|g|me msg|v o n|g|cs]; try reflexivity; exact Hn.
Qed.

Definition gstatic_form (p: TypeParameterId) (S: EType): Prop :=
    (forall C, In C (bound_components S) -> pfrag env C = true /\ bplain p C = true
        /\ forall g, C = TypeVariable g \/ C = Nullable (TypeVariable g) -> param_of g <> p)
    /\ forall cs, inter_of S = Some cs -> (forall C, In C cs -> compfrag env C = true)
        /\ components_sfrag env (map to_generic cs) = true
        /\ forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs).

(* The lower bound of p, checked against its static upper bound S (plus_static_check): not nullable
   where S isn't, as unify took it; and for bindings of the other variables of S that satisfy the
   states, of types of the fragment, not nullable where their bounds aren't, and not of the ownerships
   of the lower bound, it is below each component of S with p bound to it. Until a lower bound is
   checked, it is Nothing. *)
Definition gstatic_checked (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    is_non_nullable_nothing env (lower_bound st) = false ->
    (is_nullable env (static_upper_bound st) = false -> is_nullable env (lower_bound st) = false)
    /\ forall b, plain_values b -> (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
        nonnull_values b -> owners_free b (lower_bound st) -> vars_in (fun q => param_eqb q p || bound_b b q) (static_upper_bound st) = true ->
        gsatisfies b s ->
        forall C, In C (bound_components (static_upper_bound st)) ->
        below (lower_bound st) (instantiate_free env b (with_candidate env p (lower_bound st) C)).

(* The static upper bound of a variable: without type variables, above the upper bound; with them, of
   the form of gstatic_form, the lower bound checked against it *)
Definition gstatic_ok (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    if no_vars (static_upper_bound st) then
        forall x, of_fragment x -> below x (upper_bound st) -> below x (static_upper_bound st)
    else gstatic_form p (static_upper_bound st) /\ gstatic_checked s p st.

Definition gstate_ok (s: VariableStates) (p: TypeParameterId) (st: VariableState): Prop :=
    no_vars (upper_bound st) = true /\ no_vars (lower_bound st) = true
    /\ (is_exact st = false -> is_capturable st = false /\ below (lower_bound st) (upper_bound st)
        /\ of_fragment (upper_bound st) /\ of_fragment (lower_bound st) /\ Qb (upper_bound st) /\ Qb (lower_bound st)
        /\ bottom_only (lower_bound st) = true /\ gstatic_ok s p st)
    /\ vars_in (static_vars env p) (static_upper_bound st) = true.

(* The variable states inference works with in generic code *)
Definition gwf2 (s: VariableStates): Prop := forall p st, lookup_state s p = Some st -> gstate_ok s p st.

Lemma gwf2_capturable: forall s t, gwf2 s -> capturable t s = None.
Proof.
    intros s [| | | | |[gm nn p bnd]|] Hs; try reflexivity. simpl.
    destruct (lookup_state s p) as [st|] eqn:E; [|reflexivity].
    destruct (is_exact st) eqn:Ee; [rewrite andb_false_r; reflexivity|].
    destruct (Hs p st E) as [_ [_ [He _]]]. rewrite (proj1 (He Ee)). reflexivity.
Qed.

Lemma gwf2_ranked: forall s, gwf2 s -> ranked_states env s.
Proof. intros s Hs q st Hq. destruct (Hs q st Hq) as [H1 [H2 [_ H4]]]. auto. Qed.

Lemma gstatic_ok_mono: forall s s' p st, (forall b, gsatisfies b s' -> gsatisfies b s) -> gstatic_ok s p st -> gstatic_ok s' p st.
Proof.
    intros s s' p st Hn H. unfold gstatic_ok in *. destruct (no_vars (static_upper_bound st)); [exact H|].
    destruct H as [H1 H4]. split; [exact H1|].
    intros Hnn. split; [exact (proj1 (H4 Hnn))|].
    intros b Hb Hbf' Hnv Ho Hv Hs. exact (proj2 (H4 Hnn) b Hb Hbf' Hnv Ho Hv (Hn b Hs)).
Qed.

Lemma gwf2_set_state: forall s p st, gwf2 s -> (forall b, gsatisfies b (set_state s p st) -> gsatisfies b s) ->
    gstate_ok (set_state s p st) p st -> gwf2 (set_state s p st).
Proof.
    intros s p st Hs Hn Hst q st' Hq. destruct (Nat.eq_dec p q) as [<-|Hne].
    - rewrite lookup_set_same in Hq. injection Hq as <-. exact Hst.
    - rewrite lookup_set_other in Hq by exact Hne. destruct (Hs q st' Hq) as [H1 [H2 [H3 H4]]].
      split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
      intros E. destruct (H3 E) as [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]].
      split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
      split; [exact H11|]. exact (gstatic_ok_mono s _ q st' Hn H12).
Qed.

(* No bindings at all *)
Lemma plain_nil: plain_values [].
Proof. intros p a E. discriminate E. Qed.

Lemma bf_nil: forall q o x, lookup_binding [] q = Some (TypeArgument Model.invariant o x) -> of_fragment x.
Proof. intros q o x E. discriminate E. Qed.

Lemma owners_free_h_nil: forall (U: TypeParameterId -> Prop), (forall q, U q) -> forall t, owners_free_h [] U t.
Proof.
    intros U HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; cbn [owners_free_h]; try exact I.
    - induction args as [|a args IHa]; [exact I|]. split; [exact (IH a)|exact IHa].
    - exact (IH n).
    - exact (HU _).
    - split; [destruct o; try exact I; reflexivity|exact (IH n)].
    - induction cs as [|c cs IHc]; [exact I|]. split; [exact (IH c)|exact IHc].
Qed.

Lemma owners_free_nil: forall t, owners_free [] t.
Proof.
    assert (Hp: forall p, param_owners_free [] p).
    { intros p. unfold param_owners_free, through_param.
      generalize (S (parameter_rank env p)) as k. intros k. revert p. induction k as [|k IH]; intros p; [exact I|].
      cbn [param_level]. apply owners_free_h_nil. intros q. destruct (param_eqb q p); [exact I|exact (IH q)]. }
    intros t. rewrite owners_free_top. apply owners_free_h_nil. exact Hp.
Qed.

Lemma vars_in_mbinds: forall b t, vars_in (bound_b b) t = true -> mbinds b t.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn p vs]|cs] H; cbn [vars_in] in H; cbn [mbinds]; try exact I.
    - induction args as [|a args IHa]; [exact I|]. cbn [forallb] in H. apply andb_true_iff in H.
      split; [exact (IH a (proj1 H))|exact (IHa (proj2 H))].
    - exact (IH n H).
    - exact (IH n H).
    - apply andb_true_iff in H. destruct H as [H _]. unfold bound_b in H.
      destruct (lookup_binding b p) as [a|]; [exists a; reflexivity|discriminate H].
Qed.

(* The static upper bound with a candidate: its variables but p bound in b *)
Lemma mbinds_candidate: forall b p c S, vars_in (fun q => param_eqb q p || bound_b b q) S = true -> no_vars c = true ->
    mbinds b (with_candidate env p c S).
Proof.
    intros b p c S HS Hc. apply vars_in_mbinds.
    apply (vars_in_mono (fun q => (param_eqb q p || bound_b b q) && negb (param_eqb q p))); [|exact (candidate_vars env wf _ p c S HS Hc)].
    intros q E. apply andb_true_iff in E. destruct E as [E1 E2]. destruct (param_eqb q p); [discriminate E2|exact E1].
Qed.

(* A type variable other than p in a type argument stays as it is, with p bound *)
Lemma instantiate_other: forall p a v o gm nn q n, is_parameter_ownership o = false ->
    (n = TypeVariable (mkGenericRef gm nn q []) \/ n = Nullable (TypeVariable (mkGenericRef gm nn q []))) -> q <> p ->
    instantiate env [(p, a)] (TypeArgument v o n) = TypeArgument v o n.
Proof.
    intros p a v o gm nn q n Ho Eq Hq. destruct o as [| | |r]; [| | |discriminate Ho];
        destruct Eq as [-> | ->]; cbn [instantiate lookup_binding mentions_loosely_bound_in_arguments instantiate_ownership];
        unfold param_eqb; rewrite (proj2 (Nat.eqb_neq q p) Hq); reflexivity.
Qed.

(* The static upper bound with a candidate of the types of the arguments, a mixed type *)
Lemma mfrag_candidate: forall b p c, yfrag b c -> nonnull_values b -> forall S, ifrag env S = true -> bplain p S = true ->
    (forall g, S = TypeVariable g -> param_of g <> p) -> mfrag b (with_candidate env p c S).
Proof.
    intros b p c Hc Hnv S HS Hbp. destruct (bplain_parts p S Hbp) as [Ho [Hnw Hav]].
    clear Hbp. revert S HS Ho Hnw Hav.
    assert (Hcn: nests_argument c = false) by exact (gfrag_not_nested env c (proj1 (proj1 Hc))).
    assert (Hpp: forall q a, lookup_binding [(p, TypeArgument Model.invariant ref c)] q = Some a -> is_loose a = false).
    { intros q a E. cbn [lookup_binding] in E. destruct (param_eqb q p); [injection E as <-; reflexivity|discriminate E]. }
    assert (Hfinal: final_argument (TypeArgument Model.invariant ref c) = c).
    { unfold final_argument. cbn [is_loose Variance_beq negb orb]. rewrite Hcn. reflexivity. }
    assert (Hshape: forall n, ifrag env n = true -> nests_argument (with_candidate env p c n) = false).
    { intros n Hn. destruct (ifrag_cases env wf n Hn) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]];
          try reflexivity.
      unfold with_candidate. cbn [instantiate lookup_binding]. destruct (param_eqb q p); [rewrite Hfinal; exact Hcn|reflexivity]. }
    fix IH 1. intros [m c' args|n|g|me msg|v o n|[gm nn q vs]|cs] HS Ho Hnw Hav Htop; try discriminate HS.
    - assert (Hl: length args = length (parameter_ids env c')).
      { destruct (ifrag_cases env wf _ HS) as [[m' [c'' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
            try discriminate Heq.
        - injection Heq as <- <- <-. exact Hl.
        - unfold bottom_type in Heq. injection Heq as _ -> ->. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
      pose proof (root_args_ifrag env wf m c' args HS) as Hargs. cbn [plain_owners] in Ho.
      pose proof (args_narrowed_root env m c' args Hnw) as Hnws. pose proof (args_avoid_root p m c' args Hav) as Havs. clear HS Htop Hnw Hav.
      unfold with_candidate. cbn [instantiate mfrag]. split; [rewrite length_map; exact Hl|]. clear Hl.
      induction args as [|a args IHa]; [exact I|]. cbn [forallb] in Ho. apply andb_true_iff in Ho. destruct Ho as [Hoa Hoas].
      cbn [map fold_right]. split; [|exact (IHa Hoas (fun a' Ha' => Hargs a' (or_intror Ha')) (fun a' Ha' => Hnws a' (or_intror Ha'))
          (fun a' Ha' => Havs a' (or_intror Ha')))].
      pose proof (Hargs a (or_introl eq_refl)) as Ha. pose proof (Hnws a (or_introl eq_refl)) as Hna.
      pose proof (Havs a (or_introl eq_refl)) as Hva.
      destruct a as [| | | |v o n| |]; try discriminate Ha.
      cbn [argument_ifrag] in Ha.
      cbn [plain_owners] in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
      apply negb_true_iff in Hop.
      (* a type variable other than p, of a mutability given to it, narrowed or made nullable narrowed *)
      destruct (avoid_nfrag env p v o n Ha Hva) as [Ha'|[gm [nn [q [Hq [Eq Hs]]]]]].
      2:{ rewrite (instantiate_other p (TypeArgument Model.invariant ref c) v o gm nn q n Hop Eq Hq). right. split; [exact Hop|right].
          destruct Eq as [-> | ->]; [exact Hs|]. split; [exact Hs|].
          destruct nn; [left; reflexivity|right]. intros o' x Ex. simpl in Hna. apply negb_true_iff in Hna. exact (Hnv q o' x Ex Hna). }
      clear Ha. rename Ha' into Ha.
      pose proof (narrowed_content env v o n Hna) as Hnn. pose proof (args_avoid_argument p v o n Hva) as Hvn.
      assert (Hcase: (exists bnd', n = TypeVariable (mkGenericRef None false p bnd')) \/ (forall g, n = TypeVariable g -> param_of g <> p)).
      { destruct (ifrag_cases env wf n Ha) as [[? [? [? [-> _]]]]|[->|[[? [? [? [-> _]]]]|[q [-> _]]]]];
            try (right; intros g E; discriminate E).
        destruct (Nat.eq_dec q p) as [->|Hne]; [left; eexists; reflexivity|].
        right. intros g E. injection E as <-. exact Hne. }
      pose proof (Hshape n Ha) as Hns.
      rewrite (instantiate_unloose_argument env _ v o n Hpp).
      + assert (Eo: instantiate_ownership [(p, TypeArgument Model.invariant ref c)] o = o)
            by (destruct o; first [reflexivity|discriminate Hop]).
        rewrite Eo. destruct Hcase as [[bnd' ->]|Hnp].
        * left. cbn [instantiate lookup_binding]. rewrite param_eqb_refl, Hfinal. split; [exact Hc|].
          destruct o; first [exact I|discriminate Hop].
        * right. split; [exact Hop|left; exact (IH n Ha Hon Hnn Hvn Hnp)].
      + unfold with_candidate in Hns. destruct (instantiate env _ n) as [| | | | | |]; try reflexivity; discriminate Hns.
      + intros x Ex. unfold with_candidate in Hns. rewrite Ex in Hns. destruct x; try reflexivity; discriminate Hns.
    - assert (Hn: ifrag env n = true /\ exists m c' args, n = RootResolved m c' args).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[Heq|[[m [c' [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct Hn as [Hn Hroot]. cbn [plain_owners] in Ho.
      assert (Hnw': args_narrowed env n = true) by (destruct Hroot as [? [? [? ->]]]; exact Hnw).
      pose proof (IH n Hn Ho Hnw' Hav (fun g E => ltac:(destruct Hroot as [? [? [? E']]]; rewrite E' in E; discriminate E))) as Hm.
      destruct Hroot as [m [c' [args ->]]].
      unfold with_candidate in Hm |- *. cbn [instantiate] in Hm |- *. cbn [rewrap_nullable mfrag]. split; [reflexivity|exact Hm].
    - unfold ifrag in HS. cbn [no_generics] in HS. rewrite andb_false_r in HS. discriminate HS.
    - destruct gm, nn; try (unfold ifrag in HS; apply andb_true_iff in HS; destruct HS as [_ HS]; discriminate HS).
      assert (Hq: q <> p) by exact (Htop _ eq_refl).
      unfold with_candidate. cbn [instantiate lookup_binding]. unfold param_eqb.
      rewrite (proj2 (Nat.eqb_neq q p) Hq). exact I.
Qed.

(*
 * The static check of a candidate c, of the types of the arguments, against a static upper bound S
 * with type variables: the states it ends with work, and, whatever bindings satisfy them, c is below
 * each component of S with c in place of p and the other variables bound. Of an intersection, unify
 * gives the components that aren't type variables c, and those that are what the others don't
 * cover of it (Any of the mutability of c), or c itself (Constraints.static_whole, for class types).
 *)
(* A type of the parameters without ownerships of type parameters: variables plainly, a mixed type *)
Lemma ifrag_plain_variables: forall p S, ifrag env S = true -> bplain p S = true -> plain_variables p S.
Proof.
    intros p S HS Hbp. destruct (bplain_parts p S Hbp) as [Ho [_ Hav]]. clear Hbp. revert S HS Ho Hav.
    fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] HS Ho Hav; try discriminate HS.
    - pose proof (root_args_ifrag env wf m c args HS) as Hargs. cbn [plain_owners] in Ho. cbn [plain_variables].
      pose proof (args_avoid_root p m c args Hav) as Havs. clear HS Hav.
      induction args as [|a args IHa]; [exact I|]. cbn [forallb] in Ho. apply andb_true_iff in Ho. destruct Ho as [Hoa Hoas].
      split; [|exact (IHa Hoas (fun a' Ha' => Hargs a' (or_intror Ha')) (fun a' Ha' => Havs a' (or_intror Ha')))].
      pose proof (Hargs a (or_introl eq_refl)) as Ha. pose proof (Havs a (or_introl eq_refl)) as Hva.
      destruct a as [| | | |v o n| |]; try discriminate Ha.
      cbn [argument_ifrag] in Ha.
      cbn [plain_owners] in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
      apply negb_true_iff in Hop. split; [exact Hop|].
      destruct (avoid_nfrag env p v o n Ha Hva) as [Ha'|[gm [nn [q [Hq [[-> | ->] _]]]]]];
          [left; exact (IH n Ha' Hon (args_avoid_argument p v o n Hva))|right; exact Hq|right; exact Hq].
    - assert (Hn: ifrag env n = true /\ exists m c args, n = RootResolved m c args).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[Heq|[[m [c [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct Hn as [Hn Hroot]. cbn [plain_owners] in Ho. pose proof (IH n Hn Ho Hav) as Hp.
      destruct Hroot as [m [c [args ->]]]. cbn [plain_variables]. split; [exact Hp|exact I].
    - unfold ifrag in HS. cbn [no_generics] in HS. rewrite andb_false_r in HS. discriminate HS.
    - destruct gm, nn; try (unfold ifrag in HS; apply andb_true_iff in HS; destruct HS as [_ HS]; discriminate HS). exact I.
Qed.

Lemma ifrag_mfrag: forall b P, ifrag env P = true -> plain_owners P = true -> args_narrowed env P = true ->
    nonnull_values b -> mfrag b P.
Proof.
    intros b. fix IH 1. intros [m c args|n|g|me msg|v o n|[gm nn q vs]|cs] HS Ho Hna Hor; try discriminate HS.
    - assert (Hl: length args = length (parameter_ids env c)).
      { destruct (ifrag_cases env wf _ HS) as [[m' [c'' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
            try discriminate Heq.
        - injection Heq as <- <- <-. exact Hl.
        - unfold bottom_type in Heq. injection Heq as _ -> ->. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
      pose proof (root_args_ifrag env wf m c args HS) as Hargs. cbn [plain_owners] in Ho.
      pose proof (args_narrowed_root env m c args Hna) as Hnas.
      clear HS Hna.
      cbn [mfrag]. split; [exact Hl|]. clear Hl.
      induction args as [|a args IHa]; [exact I|]. cbn [forallb] in Ho. apply andb_true_iff in Ho. destruct Ho as [Hoa Hoas].
      split; [|exact (IHa Hoas (fun a' Ha' => Hargs a' (or_intror Ha')) (fun a' Ha' => Hnas a' (or_intror Ha')))].
      pose proof (Hargs a (or_introl eq_refl)) as Ha. pose proof (Hnas a (or_introl eq_refl)) as Hnaa.
      destruct a as [| | | |v o n| |]; try discriminate Ha.
      cbn [argument_ifrag] in Ha. cbn [plain_owners] in Hoa. apply andb_true_iff in Hoa. destruct Hoa as [Hop Hon].
      apply negb_true_iff in Hop. right. split; [exact Hop|].
      destruct (nfrag_cases env n Ha) as [Ha'|[gm [nn [q [[-> | ->] Hsq]]]]].
      + left. exact (IH n Ha' Hon (narrowed_content env v o n Hnaa) Hor).
      + right. exact Hsq.
      + right. split; [exact Hsq|]. destruct nn; [left; reflexivity|right].
        intros o' x Ex. simpl in Hnaa. apply negb_true_iff in Hnaa. exact (Hor q o' x Ex Hnaa).
    - assert (Hn: ifrag env n = true /\ exists m c args, n = RootResolved m c args).
      { destruct (ifrag_cases env wf _ HS) as [[? [? [? [Heq _]]]]|[Heq|[[m [c [args [Heq H']]]]|[? [Heq _]]]]];
            try discriminate Heq.
        injection Heq as ->. split; [exact H'|eauto]. }
      destruct Hn as [Hn Hroot]. cbn [plain_owners] in Ho.
      pose proof (IH n Hn Ho ltac:(destruct Hroot as [? [? [? ->]]]; exact Hna) Hor) as Hp.
      destruct Hroot as [m [c [args ->]]]. cbn [mfrag]. split; [reflexivity|exact Hp].
    - unfold ifrag in HS. cbn [no_generics] in HS. rewrite andb_false_r in HS. discriminate HS.
    - destruct gm, nn; try (unfold ifrag in HS; apply andb_true_iff in HS; destruct HS as [_ HS]; discriminate HS). exact I.
Qed.

(* A parameter, also of a type variable of a mutability given to it, narrowed or made nullable: what the
   instance of its type takes *)
Lemma mixed_parameter: forall b, plain_values b ->
    (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
    forall (W: VariableStates -> Prop) (HW: forall s t, W s -> capturable t s = None) n, (forall k, k < n -> mleaf b W k) ->
    forall P A s s', pfrag env P = true -> plain_owners P = true -> args_narrowed env P = true ->
        nonnull_values b -> yfrag b A -> W s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> mbinds b P -> below A (instantiate_free env b P)).
Proof.
    intros b Hpb Hbf W HW n IH P A s s' HP Ho Hna Hor HA Hs H.
    destruct (pfrag_cases env P HP) as [HP'|[[gm [nn [p [-> [Hsf _]]]]]|[gm [nn [p [-> [Hsf _]]]]]]].
    { destruct (proj1 (mixed_arguments b Hpb Hbf W HW n IH) P A s s' (ifrag_mfrag b P HP' Ho Hna Hor) HA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. exact H3. }
    all: assert (Hstep: forall k A0, k < n -> yfrag b A0 ->
        unify env (S k) (TypeVariable (mkGenericRef gm nn p [])) A0 (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> forall o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> below A0 (ref_apply env gm nn x))).
    all: try (intros k A0 Hk HA0 H0;
        assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I);
        destruct (unify_variable_given env wf k gm nn p A0 s s' Hsh H0) as [H1 [Hgm Hnul]];
        destruct (proj1 (IH k Hk) p [] A0 s s' Hs HA0 H1) as [Hs' [Hext Hsound]];
        split; [exact Hs'|]; split; [exact Hext|]; intros Hsb o x Ex;
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]];
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> gfits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit);
        exact (reference_below gm nn p A0 x (proj1 HA0) Hx Hsf Hgm (fun _ => Hnul) (Hsound o x Hx Hfits))).
    all: assert (Ei: forall a, lookup_binding b p = Some a -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ instantiate_free env b (TypeVariable (mkGenericRef gm nn p [])) = ref_apply env gm nn x
        /\ instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn p []))) = rewrap_nullable (ref_apply env gm nn x)
        /\ of_fragment x).
    all: try (intros a Ea; destruct (Hpb p a Ea) as [Hl [o [x [-> Hy]]]]; exists o, x; split; [exact Ea|];
        split; [cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity|];
        split; [cbn [instantiate_free]; rewrite Ea; unfold final_argument; rewrite Hl, Hy; reflexivity|exact (Hbf p o x Ea)]).
    - destruct n as [|n]; [discriminate H|]. destruct (Hstep n A (Nat.lt_succ_diag_r n) HA H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ea]. destruct (Ei a Ea) as [o [x [Ex [Exi _]]]].
      rewrite Exi. exact (Hsnd Hsb o x Ex).
    - (* made nullable: the variable takes the argument without null *)
      destruct n as [|n]; [discriminate H|].
      rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct n as [|n]; [discriminate H|].
      destruct (Hstep n _ ltac:(lia) (yfrag_nullable_assignee b A HA) H) as [Hs' [Hext Hsnd]].
      split; [exact Hs'|]. split; [exact Hext|]. intros Hsb [a Ea]. destruct (Ei a Ea) as [o [x [Ex [_ [Exn Hx]]]]].
      rewrite Exn.
      exact (nullable_variable_below false A _ (proj1 (proj1 HA)) (proj1 (ref_apply_of_fragment gm nn x Hx)) (Hsnd Hsb o x Ex)).
Qed.

(* A type whose type variables are all bound, none of which it mentions, has none *)
Lemma bound_unmentioned_closed: forall b t, vars_in (bound_b b) t = true -> mentions_bound b t = false -> no_vars t = true.
Proof.
    intros b. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Hv Hm;
        cbn [vars_in mentions_bound no_vars] in Hv, Hm |- *.
    - induction args as [|a args IHa]; [reflexivity|]. cbn [forallb existsb] in Hv, Hm |- *.
      apply andb_true_iff in Hv. apply orb_false_iff in Hm. rewrite (IH a (proj1 Hv) (proj1 Hm)). exact (IHa (proj2 Hv) (proj2 Hm)).
    - exact (IH n Hv Hm).
    - exact Hv.
    - reflexivity.
    - apply orb_false_iff in Hm. exact (IH n Hv (proj2 Hm)).
    - unfold bound_b in Hv. destruct (lookup_binding b p); [discriminate Hm|discriminate Hv].
    - induction cs as [|c cs IHc]; [reflexivity|]. cbn [forallb existsb] in Hv, Hm |- *.
      apply andb_true_iff in Hv. apply orb_false_iff in Hm. rewrite (IH c (proj1 Hv) (proj1 Hm)). exact (IHc (proj2 Hv) (proj2 Hm)).
Qed.

(* An intersection as the type of a parameter, with bindings of plain values: the argument A is below
   the instance of each component, as gparam_components; and A is non-null *)
Lemma mparam_components: forall b, plain_values b ->
    (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
    forall (W: VariableStates -> Prop) (HW: forall s t, W s -> capturable t s = None) n, (forall k, k < n -> mleaf b W k) ->
    forall cs A s s', (forall C, In C cs -> compfrag env C = true) -> components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> plain_owners C = true /\ args_narrowed env C = true) ->
    nonnull_values b -> yfrag b A -> W s ->
    unify env n (Intersection cs) A (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ is_nullable env A = false
    /\ (gsatisfies b s' -> forall C, In C cs -> mbinds b C -> below A (instantiate_free env b C)).
Proof.
    intros b Hpb Hbf W HW n IH cs A s s' HSi Hcs Hcn Hcor HA Hs H.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])))
        by (intros C HC; exact (param_component_cases env wf cs C HSi Hcs HC)).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [reflexivity|exact Hsh]. }
    pose proof HA as [Ha [Hba [Hoa Hqa]]].
    assert (Haa: assignee_mutability env A = assignment_mutability env A)
        by (destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; reflexivity).
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match A with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists an, A = Nullable an).
    { destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[an [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[an Ean]].
    2:{ (* a nullable argument, for a non-null intersection *)
        assert (Hin: is_nullable env (Intersection cs) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|].
          exact (intersection_not_nullable env (C0 :: cs0) C0 (or_introl eq_refl) (Hnull C0 (or_introl eq_refl))). }
        subst A. rewrite (unify_not_nullable_intersection env n1 cs _ s Hin) in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body _ _ _ A s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    (* the components that aren't type variables: mixed types *)
    assert (Hns: forall x, In x ns -> forall s0 s0', W s0 -> unify env n1 x A (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
        /\ (gsatisfies b s0' -> mbinds b x -> below A (instantiate_free env b x))).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      exact (proj1 (mixed_arguments b Hpb Hbf W HW n1 (fun k Hk => IH k ltac:(lia))) x A s0 s0'
          (ifrag_mfrag b x (compfrag_ifrag env x (HSi x Hx) Hv) (proj1 (Hcn x Hx)) (proj2 (Hcn x Hx)) Hcor) HA Hs0 E0). }
    destruct (fold_unify (fun inner component => unify env n1 component A inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (gfold_list W (fun x inner => unify env n1 x A inner) ns s s2 (fun x => unify_keeps_failure env n1 x A)
        (fun x s0 s0' Hx Hs0 E0 => let H' := Hns x Hx s0 s0' Hs0 E0 in conj (proj1 H') (proj1 (proj2 H'))) Hs E2) as [Hs2 [Hn2 Hall2]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, W s3 /\ (forall b', gsatisfies b' s3 -> gsatisfies b' s2)
        /\ yfrag b na /\ below A na /\ (na = A \/ is_nullable env A = false)
        /\ is_subtype_of (assignee_mutability env A) (assignee_mutability env na) = true
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component A inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component A (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of A, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Ecov) as [Hs3 [Hn3 _]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        destruct (Hcase cov Hcov) as [[mc [cl1 [argsc ->]]]|[gm [nn [q ->]]]]; [|discriminate Hv].
        destruct (root_takes n1 mc cl1 argsc A s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn', andb_false_r in H.
        set (m' := intersect_mutability (mutability_of env A) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': is_subtype_of (assignment_mutability env A) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked A).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hn3|].
        split; [split; [exact (any_of_fragment m')|]|].
        { split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
          split; [exact I|exact (Qb_any m')]. }
        split; [exact (below_any_of _ _ Ha Hcn' Hm')|]. split; [right; exact Hcn'|].
        split; [|exact H]. rewrite Haa. cbn [assignee_mutability assignment_mutability or_readonly].
        rewrite (wf_any_is_not_const env wf). exact Hm'.
      - (* nothing covers: the variables take A *)
        exists A, s2. split; [exact Hs2|]. split; [auto|]. split; [exact HA|].
        split; [exact (below_refl A Ha)|]. split; [left; reflexivity|]. split; [apply mutability_is_subtype_of_refl|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hn3 [Hyna [Hcna [Hnna [Hnam Hfold]]]]]]]].
    set (VSound := fun x u => forall gm nn q, x = TypeVariable (mkGenericRef gm nn q []) ->
        (forall o y, of_fragment y -> (forall st, lookup_state u q = Some st -> gfits st o y) -> below A y)
        /\ is_nullable env A = false
        /\ (forall m, gm = Some m -> is_subtype_of (assignee_mutability env A) m = true)).
    assert (Hvs: forall x, In x vs -> forall s0 s0', W s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x A (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ VSound x s0').
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      destruct (Hcase x Hx) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [discriminate Hv|].
      destruct n1 as [|n2]; [discriminate E0|].
      assert (Hone: forall A0, yfrag b A0 -> (forall y, of_fragment y -> below A0 y -> below A y) -> (A0 = A \/ is_nullable env A = false) ->
          is_subtype_of (assignee_mutability env A) (assignee_mutability env A0) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s0) = Some (Ongoing s0') ->
          W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ VSound (TypeVariable (mkGenericRef gm nn q [])) s0').
      { intros A0 HA0 Hthr HAa HAm EA.
        assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
        destruct (unify_variable_given env wf n2 gm nn q A0 s0 s0' Hsh EA) as [EA' [HAg Hnul]].
        destruct (proj1 (IH n2 ltac:(lia)) q [] A0 s0 s0' Hs0 HA0 EA') as [Hs0' [Hn0 Hsnd]].
        split; [exact Hs0'|]. split; [exact Hn0|].
        intros gm' nn' q' Eq. injection Eq as <- <- <-. split; [intros o y Hy Hfit; exact (Hthr y Hy (Hsnd o y Hy Hfit))|].
        split.
        - (* the component is non-null, so is A *)
          destruct HAa as [->|Ha']; [|exact Ha'].
          destruct (is_nullable env A) eqn:En; [|reflexivity].
          rewrite (Hnull _ Hx) in Hnul. discriminate (Hnul eq_refl).
        - intros m Em. exact (mutability_subtype_trans _ _ _ HAm (HAg m Em)). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena; try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->.
        exact (Hone na Hyna (fun y Hy E => below_trans A na y Ha (proj1 Hyna) Hy Hcna E) Hnna Hnam Ena).
      - exact (Hone A HA (fun y _ E => E) (or_introl eq_refl) (mutability_is_subtype_of_refl _) E0). }
    assert (Hgf: forall x, (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        x Failed = Some Failed).
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    destruct (gfold_list W (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        vs s3 s' Hgf (fun x s0 s0' Hx Hs0 E0 => let H' := Hvs x Hx s0 s0' Hs0 E0 in conj (proj1 H') (proj1 (proj2 H'))) Hs3 Hfold)
        as [Hs' [Hn' Hallv]].
    split; [exact Hs'|]. split; [intros b' Hb'; apply Hn2, Hn3, Hn', Hb'|].
    split.
    - (* A is non-null: a component takes it *)
      assert (Hne: exists C1, In C1 cs) by (destruct cs as [|C1 cs']; [simpl in Hlen; lia|exists C1; left; reflexivity]).
      destruct Hne as [C1 HC1]. destruct (Hcase C1 HC1) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      + assert (Hin: In C1 ns) by (apply filter_In; split; [exact HC1|rewrite EC; reflexivity]).
        destruct (Hall2 _ Hin) as [s0 [s0' [_ [E0 _]]]]. rewrite EC in E0.
        exact (proj1 (root_takes n1 m cl args A s0 s0' (proj1 Ha) E0)).
      + assert (Hin: In C1 vs) by (apply filter_In; split; [exact HC1|rewrite EC; reflexivity]).
        destruct (Hallv _ Hin) as [s0 [s0' [Hs0 [E0 _]]]].
        destruct (Hvs _ Hin s0 s0' Hs0 E0) as [_ [_ HQ]]. exact (proj1 (proj2 (HQ gm nn q EC))).
    - intros Hsb C HC Hmb. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      + (* a class type *)
        assert (Hin: In C ns) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
        destruct (Hall2 _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
        exact (proj2 (proj2 (Hns C Hin s0 s0' Hs0 E0)) (Hext0 b (Hn3 b (Hn' b Hsb))) Hmb).
      + (* a type variable: the type it is bound to, of the mutability given to it and narrowed or not *)
        assert (Hin: In C vs) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
        destruct (Hallv _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
        destruct (Hvs _ Hin s0 s0' Hs0 E0) as [_ [_ HQ]].
        destruct (HQ gm nn q EC) as [HVq [HnA Ham]].
        pose proof (HSi C HC) as HCf. rewrite EC in HCf, Hmb. destruct Hmb as [a Ea].
        destruct (Hpb q a Ea) as [_ [o [y [-> _]]]].
        rewrite EC, (free_variable_any b Hpb gm nn q [] o y Ea).
        destruct (Hext0 b Hsb q o y Ea) as [Hy [st [Hl Hfit]]].
        pose proof (HVq o y Hy (fun st' Hl' => ltac:(rewrite Hl in Hl'; injection Hl' as <-; exact Hfit))) as Hay.
        destruct (compfrag_cases env _ HCf) as [Hif|[gm' [nn' [q'' [Eq' [Hsq _]]]]]].
        { unfold ifrag in Hif. destruct gm, nn; cbn [no_generics] in Hif; rewrite ?andb_false_r in Hif; try discriminate Hif. exact Hay. }
        injection Eq' as <- <- <-.
        exact (reference_below gm nn q A y Ha Hy Hsq Ham (fun _ E => ltac:(rewrite HnA in E; discriminate E)) Hay).
Qed.

(* A parameter of any type of qfrag, with bindings of plain values: what the instance of its type
   takes; of an intersection, nullable or not, as ofComponents makes the instance, or the intersection
   itself where it mentions nothing bound *)
Lemma mqparameter: forall b, plain_values b ->
    (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
    forall (W: VariableStates -> Prop) (HW: forall s t, W s -> capturable t s = None) n, (forall k, k < n -> mleaf b W k) ->
    forall P A s s', qfrag env P = true -> (forall C, In C (intersected_components P) -> plain_owners C = true) ->
        args_narrowed env P = true -> nonnull_values b -> yfrag b A -> W s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> vars_in (bound_b b) P = true -> below A (instantiate_free env b P)).
Proof.
    intros b Hpb Hbf W HW n IH P A s s' HQ Ho Hna Hor HA Hs H.
    destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]].
    { pose proof (Ho P ltac:(rewrite (intersected_none P (pfrag_not_inter env P HP)); left; reflexivity)) as HoP.
      destruct (mixed_parameter b Hpb Hbf W HW n IH P A s s' HP HoP Hna Hor HA Hs H) as [H1 [H2 H3]].
      split; [exact H1|]. split; [exact H2|]. intros Hsb Hv. exact (H3 Hsb (vars_in_mbinds b P Hv)). }
    assert (Hcn: forall C, In C cs -> plain_owners C = true /\ args_narrowed env C = true).
    { intros C HC. split; [destruct EP as [-> | ->]; [exact (Ho C HC)|exact (Ho (Nullable C) (in_map Nullable _ _ HC))]|].
      assert (E: forallb (nullable_narrowed env) cs = true) by (destruct EP as [-> | ->]; exact Hna).
      rewrite forallb_forall in E.
      destruct C as [m c args|[m c args|n'|g|me msg|v o n'|g|cs']|g|me msg|v o n'|g|cs']; try reflexivity; exact (E _ HC). }
    (* below the instance of each component, below that of the intersection *)
    assert (Hinter: forall k A0, k <= n -> yfrag b A0 -> unify env k (Intersection cs) A0 (Ongoing s) = Some (Ongoing s') ->
        W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> vars_in (bound_b b) (Intersection cs) = true -> below A0 (instantiate_free env b (Intersection cs)))).
    { intros k A0 Hk HA0 E.
      destruct (mparam_components b Hpb Hbf W HW k (fun j Hj => IH j ltac:(lia)) cs A0 s s' HSi Hcs Hcn Hor HA0 Hs E)
          as [Hs' [Hn' [HnA Hall]]].
      split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb Hv.
      assert (HvC: forall C, In C cs -> vars_in (bound_b b) C = true)
          by (cbn [vars_in] in Hv; rewrite forallb_forall in Hv; exact Hv).
      cbn [instantiate_free]. destruct (existsb (mentions_bound b) cs) eqn:Em.
      - destruct (components_sfrag_facts env _ Hcs) as [Hl _]. rewrite length_map in Hl.
        refine (proj1 (below_of_components A0 _ (proj1 HA0) HnA ltac:(rewrite length_map; exact Hl) _)).
        intros y Hy. apply in_map_iff in Hy. destruct Hy as [C [<- HC]].
        split; [|exact (Hall Hsb C HC (vars_in_mbinds b C (HvC C HC)))].
        destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
        + exact (mixed_of_fragment b Hpb Hbf C
              (ifrag_mfrag b C (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) (proj1 (Hcn C HC)) (proj2 (Hcn C HC))
                  Hor)
              (vars_in_mbinds b C (HvC C HC))).
        + pose proof (HvC C HC) as HvT. rewrite EC in HvT |- *. cbn [vars_in] in HvT. rewrite andb_true_r in HvT.
          unfold bound_b in HvT. destruct (lookup_binding b q) as [a|] eqn:Ea; [|discriminate HvT].
          destruct (Hpb q a Ea) as [_ [o [x [-> _]]]].
          rewrite (free_variable_any b Hpb gm nn q [] o x Ea). exact (ref_apply_of_fragment gm nn x (Hbf q o x Ea)).
      - (* it mentions nothing bound, so no type variables: as unify checked it *)
        assert (Hnv: no_vars (Intersection cs) = true).
        { cbn [no_vars]. apply forallb_forall. intros C HC. apply (bound_unmentioned_closed b C (HvC C HC)).
          destruct (mentions_bound b C) eqn:EmC; [|reflexivity].
          rewrite (proj2 (existsb_exists _ _) (ex_intro _ C (conj HC EmC))) in Em. discriminate Em. }
        destruct (keeps_free env wf k _ A0 s s' Hnv (of_fragment_no_vars A0 (proj1 HA0)) E) as [_ E0]. exists k. exact E0. }
    destruct EP as [->| ->].
    - exact (Hinter n A (le_n n) HA H).
    - (* nullable: the intersection takes the argument without null *)
      destruct n as [|n]; [discriminate H|]. rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct (Hinter n _ (Nat.le_succ_diag_r n) (yfrag_nullable_assignee b A HA) H) as [Hs' [Hn' Hsnd]].
      split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb Hv.
      change (instantiate_free env b (Nullable (Intersection cs))) with (rewrap_nullable (instantiate_free env b (Intersection cs))).
      exact (nullable_below A _ (proj1 (proj1 HA)) (Hsnd Hsb Hv)).
Qed.

(* The parameter types of pfrag, without ownerships of type parameters, as those of qfrag *)
Lemma pfrag_params: forall P, pfrag env P = true -> plain_owners P = true ->
    qfrag env P = true /\ forall C, In C (intersected_components P) -> plain_owners C = true.
Proof.
    intros P HP Ho. split; [exact (pfrag_qfrag env P HP)|].
    rewrite (intersected_none P (pfrag_not_inter env P HP)). intros C [<-|[]]. exact Ho.
Qed.

(* A narrowed type variable is not nullable, of any mutability given to it *)
Lemma narrowed_variable_not_nullable: forall gm q, is_nullable env (TypeVariable (mkGenericRef gm true q [])) = false.
Proof.
    intros gm q. rewrite (is_nullable_type_variable env ranked), <- (nullable_generic env wf).
    exact (proj2 (proj2 (narrowed_ref env wf declared declared_wf gm true q))).
Qed.

(* What a type variable takes isn't nullable where the variable isn't *)
Lemma variable_takes_not_nullable: forall n gm nn q a s s', gfrag env a = true ->
    unify env n (TypeVariable (mkGenericRef gm nn q [])) a (Ongoing s) = Some (Ongoing s') ->
    is_nullable env (TypeVariable (mkGenericRef gm nn q [])) = false -> is_nullable env a = false.
Proof.
    intros [|n] gm nn q a s s' Ha H Hn; [discriminate H|].
    assert (Hsh: match a with Error _ _ | TypeVariable _ => False | _ => True end)
        by (destruct (gfrag_cases env a Ha) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
    destruct (unify_variable_given env wf n gm nn q a s s' Hsh H) as [_ [_ Hnul]].
    destruct (is_nullable env a); [rewrite (Hnul eq_refl) in Hn; discriminate Hn|reflexivity].
Qed.

(* ... and so what a type of ifrag other than p takes, with a candidate for p in it *)
Lemma ifrag_candidate_not_nullable: forall n p c S a s s', ifrag env S = true -> (forall g, S = TypeVariable g -> param_of g <> p) ->
    gfrag env a = true -> is_nullable env S = false ->
    unify env n (with_candidate env p c S) a (Ongoing s) = Some (Ongoing s') -> is_nullable env a = false.
Proof.
    intros n p c S a s s' HS Htop Ha Hn H.
    destruct (ifrag_cases env wf S HS) as [[m [c' [args [-> _]]]]|[->|[[m [c' [args [-> _]]]]|[q [-> _]]]]].
    - unfold with_candidate in H. cbn [instantiate] in H. exact (proj1 (root_takes n _ _ _ a s s' Ha H)).
    - unfold bottom_type, with_candidate in H. cbn [instantiate] in H. exact (proj1 (root_takes n _ _ _ a s s' Ha H)).
    - simpl in Hn. discriminate Hn.
    - pose proof (Htop _ eq_refl) as Hq. cbn [param_of] in Hq. rewrite (proj1 (candidate_reference env p c None false q Hq)) in H.
      exact (variable_takes_not_nullable n None false q a s s' Ha H Hn).
Qed.

(* The static check of a candidate c against an intersection that is its static upper bound, of the
   assignee a (c, or what a nullable type unifies its nested type with of c, for a nullable
   intersection): a isn't nullable, as the intersection isn't; and whatever bindings of non-null
   values satisfy the states it ends with, a is below the instance of each component with the
   candidate in it *)
Lemma gstatic_components: forall (W: VariableStates -> Prop), (forall s t, W s -> capturable t s = None) ->
    forall n p cs c a s s', (forall k, k < n -> forall b, mleaf b W k) ->
    (forall C, In C cs -> compfrag env C = true /\ bplain p C = true /\ forall g, C = TypeVariable g -> param_of g <> p) ->
    components_sfrag env (map to_generic cs) = true ->
    (forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)) ->
    of_fragment c -> bottom_only c = true -> Qb c -> (forall b, owners_free b c -> yfrag b a) -> W s ->
    unify env n (with_candidate env p c (Intersection cs)) a (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ is_nullable env a = false
    /\ forall b, plain_values b -> (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
        nonnull_values b ->
        owners_free b c -> vars_in (fun q => param_eqb q p || bound_b b q) (Intersection cs) = true -> gsatisfies b s' ->
        forall C, In C cs -> below a (instantiate_free env b (with_candidate env p c C)).
Proof.
    intros W HW n p cs c a s s' Hleaf Hcomp Hcs Hunif Hc Hbc Hqc Hya Hs H.
    assert (Hyc: forall b, owners_free b c -> yfrag b c)
        by (intros b Hob; split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars c Hc) as Hnc.
    destruct (Hya [] (owners_free_nil c)) as [Ha [Hba [_ Hqa]]].
    assert (Haa: assignee_mutability env a = assignment_mutability env a)
        by (destruct (gfrag_cases env a (proj1 Ha)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; reflexivity).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    assert (HSi: forall C, In C cs -> compfrag env C = true) by (intros C HC; exact (proj1 (Hcomp C HC))).
    assert (Hnp: forall g, In (TypeVariable g) cs -> param_of g <> p)
        by (intros g Hg; exact (proj2 (proj2 (Hcomp _ Hg)) g eq_refl)).
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases env wf p cs C HSi Hcs Hnp HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    set (m0 := assignment_mutability env (Intersection cs)) in *.
    set (w := fun C => with_mutability env m0 (with_candidate env p c C)) in H.
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match a with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists cn, a = Nullable cn).
    { destruct (gfrag_cases env a (proj1 Ha)) as [[? [? [? ->]]]|[[cn [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[cn Ecn]].
    2:{ (* a nullable candidate, for a non-null bound *)
        assert (Hwn: is_nullable env (Intersection (map w cs)) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|]. apply (intersection_not_nullable env (map w (C0 :: cs0)) (w C0) (or_introl eq_refl)).
          unfold w. rewrite (proj1 (proj2 (with_mutability_keeps env ranked _ _))).
          destruct (Hcase C0 (or_introl eq_refl)) as [[m [cl [args ->]]]|[gm [nn [q [-> Hq]]]]].
          - unfold with_candidate. cbn [instantiate]. reflexivity.
          - rewrite (proj1 (candidate_reference env p c gm nn q Hq)). exact (Hnull _ (or_introl eq_refl)). }
        subst a. rewrite unify_step_once in H. unfold unify_step, unify_intersection in H. rewrite Hwn in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body _ _ _ a s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) (map w cs)) in H.
    set (vs := filter is_type_variable (map w cs)) in H.
    (* the components that aren't type variables: the candidate in the bound, unified with it *)
    assert (Hroot: forall C, In C cs -> is_type_variable (w C) = false -> forall s0 s0', W s0 ->
        unify env n1 (w C) a (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
        /\ forall b, plain_values b -> (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
            nonnull_values b -> owners_free b c -> vars_in (fun q => param_eqb q p || bound_b b q) C = true ->
            gsatisfies b s0' -> below a (instantiate_free env b (with_candidate env p c C))).
    { intros C HC Hv s0 s0' Hs0 E0. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      2:{ unfold w in Hv. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)) in Hv. discriminate Hv. }
      assert (Ew: unify env n1 (w C) a (Ongoing s0) = unify env n1 (with_candidate env p c C) a (Ongoing s0)).
      { pose proof (Hunif C HC) as Hu. unfold w. rewrite EC in Hu |- *. unfold with_candidate.
        cbn [instantiate with_mutability]. apply unify_root_mutability_any; [exact (proj1 Ha)|].
        cbn [assignment_mutability] in Hu |- *. destruct (is_const (declaration_of env cl)); [reflexivity|exact (eq_sym Hu)]. }
      rewrite Ew in E0. destruct (Hcomp C HC) as [HCf [HCo HCt]].
      pose proof (compfrag_ifrag env C HCf ltac:(rewrite EC; reflexivity)) as HCi.
      destruct (proj1 (mixed_arguments [] plain_nil bf_nil W HW n1 (fun k Hk => Hleaf k ltac:(lia) []))
          _ a s0 s0' (mfrag_candidate [] p c (Hyc [] (owners_free_nil c)) nonnull_nil C HCi HCo HCt) (Hya [] (owners_free_nil c)) Hs0 E0)
          as [Hs0' [Hn0 _]].
      split; [exact Hs0'|]. split; [exact Hn0|].
      intros b Hpb Hbf Hnv Hob Hvb Hsb.
      destruct (proj1 (mixed_arguments b Hpb Hbf W HW n1 (fun k Hk => Hleaf k ltac:(lia) b))
          _ a s0 s0' (mfrag_candidate b p c (Hyc b Hob) Hnv C HCi HCo HCt) (Hya b Hob) Hs0 E0) as [_ [_ Hsnd]].
      exact (Hsnd Hsb (mbinds_candidate b p c C Hvb Hnc)). }
    assert (Hns: forall x, In x ns -> forall s0 s0', W s0 -> unify env n1 x a (Ongoing s0) = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      apply in_map_iff in Hx. destruct Hx as [C0 [<- HC0]].
      destruct (Hroot C0 HC0 Hv s0 s0' Hs0 E0) as [Hs0' [Hn0 _]]. split; [exact Hs0'|exact Hn0]. }
    destruct (fold_unify (fun inner component => unify env n1 component a inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (gfold_list W (fun x inner => unify env n1 x a inner) ns s s2 (fun x => unify_keeps_failure env n1 x a)
        (fun x s0 s0' Hx Hs0 E0 => Hns x Hx s0 s0' Hs0 E0) Hs E2) as [Hs2 [Hn2 Hall2]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, W s3 /\ (forall b', gsatisfies b' s3 -> gsatisfies b' s2)
        /\ of_fragment na /\ bottom_only na = true /\ Qb na /\ below a na /\ (na = a \/ is_nullable env a = false)
        /\ is_subtype_of (assignee_mutability env a) (assignee_mutability env na) = true
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component a inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component a (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of c, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Ecov) as [Hs3 Hn3].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        apply in_map_iff in Hcov. destruct Hcov as [C1 [EC1 HC1]].
        destruct (Hcase C1 HC1) as [[m1 [cl1 [args1 EC]]]|[gm [nn [q [EC Hq]]]]].
        2:{ subst cov. unfold w in Hv. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)) in Hv. discriminate Hv. }
        assert (Ecov': exists mc argsc, cov = RootResolved mc cl1 argsc).
        { subst cov. unfold w. rewrite EC. unfold with_candidate. cbn [instantiate with_mutability]. eauto. }
        destruct Ecov' as [mc [argsc ->]].
        destruct (root_takes n1 mc cl1 argsc a s2 s3 (proj1 Ha) Ecov) as [Hcn Hcm].
        rewrite Hcn, andb_false_r in H.
        set (m' := intersect_mutability (mutability_of env a) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': is_subtype_of (assignment_mutability env a) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked a).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hn3|]. split; [exact (any_of_fragment m')|].
        split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
        split; [exact (Qb_any m')|]. split; [exact (below_any_of _ _ Ha Hcn Hm')|]. split; [right; exact Hcn|].
        split; [|exact H]. rewrite Haa. cbn [assignee_mutability assignment_mutability or_readonly].
        rewrite (wf_any_is_not_const env wf). exact Hm'.
      - (* nothing covers: the variables take c *)
        exists a, s2. split; [exact Hs2|]. split; [auto|]. split; [exact Ha|]. split; [exact Hba|]. split; [exact Hqa|].
        split; [exact (below_refl a Ha)|]. split; [left; reflexivity|]. split; [apply mutability_is_subtype_of_refl|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hn3 [Hfna [Hbna [Hqna [Hcna [Hnna [Hnam Hfold]]]]]]]]]].
    assert (Hyna: yfrag [] na) by (split; [exact Hfna|]; split; [exact Hbna|]; split; [exact (owners_free_nil na)|exact Hqna]).
    pose proof (Hya [] (owners_free_nil c)) as Hyc0.
    (* the type variables among the components: what they take, c is below *)
    set (VSound := fun q u => forall o y, of_fragment y -> (forall st, lookup_state u q = Some st -> gfits st o y) -> below a y).
    assert (Hvs: forall x, In x vs -> forall s0 s0', W s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x a (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
        /\ forall nn q, x = TypeVariable (mkGenericRef (Some m0) nn q []) -> VSound q s0' /\ (nn = true -> is_nullable env a = false)
            /\ is_subtype_of (assignee_mutability env a) m0 = true).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      apply in_map_iff in Hx. destruct Hx as [C0 [EC0 HC0]].
      destruct (Hcase C0 HC0) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      { subst x. unfold w in Hv. rewrite EC in Hv. unfold with_candidate in Hv. cbn in Hv. discriminate Hv. }
      assert (Ex: x = TypeVariable (mkGenericRef (Some m0) nn q [])).
      { subst x. unfold w. rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)). reflexivity. }
      rewrite Ex in E0 |- *. destruct n1 as [|n2]; [discriminate E0|].
      assert (Hone: forall A, yfrag [] A -> (forall y, of_fragment y -> below A y -> below a y) -> (A = a \/ is_nullable env a = false) ->
          is_subtype_of (assignee_mutability env a) (assignee_mutability env A) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) A (Ongoing s0) = Some (Ongoing s0') ->
          W s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
          /\ forall nn' q', TypeVariable (mkGenericRef (Some m0) nn q []) = TypeVariable (mkGenericRef (Some m0) nn' q' []) ->
              VSound q' s0' /\ (nn' = true -> is_nullable env a = false) /\ is_subtype_of (assignee_mutability env a) m0 = true).
      { intros A HA Hthr HAa HAm EA.
        assert (Hsh: match A with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
        destruct (unify_variable_given env wf n2 (Some m0) nn q A s0 s0' Hsh EA) as [EA' [HAg Hnul]].
        destruct (proj1 (Hleaf n2 ltac:(lia) []) q [] A s0 s0' Hs0 HA EA') as [Hs0' [Hn0 Hsnd]].
        split; [exact Hs0'|]. split; [exact Hn0|].
        intros nn' q' Eq. injection Eq as <- <-. split; [intros o y Hy Hfit; exact (Hthr y Hy (Hsnd o y Hy Hfit))|].
        split; [|exact (mutability_subtype_trans _ _ _ HAm (HAg m0 eq_refl))].
        (* narrowed, the variable takes no nullable type *)
        intros ->. destruct HAa as [->|Ha']; [|exact Ha'].
        destruct (is_nullable env a) eqn:En; [|reflexivity].
        rewrite (narrowed_variable_not_nullable (Some m0) q) in Hnul. discriminate (Hnul eq_refl). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef (Some m0) nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena;
          try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->. exact (Hone na Hyna (fun y Hy E => below_trans a na y Ha Hfna Hy Hcna E) Hnna Hnam Ena).
      - exact (Hone a Hyc0 (fun y _ E => E) (or_introl eq_refl) (mutability_is_subtype_of_refl _) E0). }
    assert (Hgf: forall x, (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x a inner | r => r end)
        x Failed = Some Failed).
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    destruct (gfold_list W (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x a inner | r => r end)
        vs s3 s' Hgf (fun x s0 s0' Hx Hs0 E0 => let H' := Hvs x Hx s0 s0' Hs0 E0 in conj (proj1 H') (proj1 (proj2 H'))) Hs3 Hfold)
        as [Hs' [Hn' Hallv]].
    split; [exact Hs'|]. split; [intros b' Hb'; apply Hn2, Hn3, Hn', Hb'|].
    split.
    { (* not nullable: a component that isn't a type variable takes a, or, where none covers it, one that is *)
      destruct Hnna as [Ena|Hna]; [subst na|exact Hna].
      assert (HC0: exists C0, In C0 cs) by (clear - Hlen; destruct cs as [|C0 cs0]; [simpl in Hlen; lia|exists C0; left; reflexivity]).
      destruct HC0 as [C0 HC0].
      destruct (Hcase C0 HC0) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
      - assert (Hv: is_type_variable (w C0) = false) by (unfold w; rewrite EC; reflexivity).
        assert (Hin: In (w C0) ns) by (apply filter_In; split; [exact (in_map w cs C0 HC0)|rewrite Hv; reflexivity]).
        destruct (Hall2 _ Hin) as [s0 [s0' [_ [E0 _]]]].
        unfold w in E0. rewrite EC in E0. unfold with_candidate in E0. cbn [instantiate with_mutability] in E0.
        exact (proj1 (root_takes n1 _ _ _ a s0 s0' (proj1 Ha) E0)).
      - assert (Ex: w C0 = TypeVariable (mkGenericRef (Some m0) nn q []))
            by (unfold w; rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)); reflexivity).
        assert (Hin: In (w C0) vs) by (apply filter_In; split; [exact (in_map w cs C0 HC0)|rewrite Ex; reflexivity]).
        destruct (Hallv _ Hin) as [s0 [s0' [_ [E0 _]]]]. rewrite Ex in E0. cbn beta in E0.
        destruct (unify env n1 (TypeVariable (mkGenericRef (Some m0) nn q [])) a (Ongoing s0)) as [[u|]|] eqn:Eu; try discriminate E0.
        apply (variable_takes_not_nullable n1 (Some m0) nn q a s0 u (proj1 Ha) Eu).
        rewrite <- Ex. unfold w. rewrite (proj1 (proj2 (with_mutability_keeps env ranked _ _))), EC, (proj1 (candidate_reference env p c gm nn q Hq)).
        rewrite <- EC. exact (Hnull C0 HC0). }
    intros b Hpb Hbf Hnv Hob Hvb Hsb C HC.
    assert (HvC: vars_in (fun q => param_eqb q p || bound_b b q) C = true)
        by (cbn [vars_in] in Hvb; rewrite forallb_forall in Hvb; exact (Hvb C HC)).
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]].
    - (* a class type *)
      assert (Hv: is_type_variable (w C) = false) by (unfold w; rewrite EC; reflexivity).
      assert (Hin: In (w C) ns) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Hv; reflexivity]).
      destruct (Hall2 _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
      exact (proj2 (proj2 (Hroot C HC Hv s0 s0' Hs0 E0)) b Hpb Hbf Hnv Hob HvC (Hext0 b (Hn3 b (Hn' b Hsb)))).
    - (* a type variable, narrowed or not: the type it is bound to, without null where it is narrowed *)
      assert (Ew: w C = TypeVariable (mkGenericRef (Some m0) nn q []))
          by (unfold w; rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)); reflexivity).
      assert (Hin: In (w C) vs) by (apply filter_In; split; [exact (in_map w cs C HC)|rewrite Ew; reflexivity]).
      destruct (Hallv _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
      destruct (Hvs _ Hin s0 s0' Hs0 E0) as [_ [_ HQ]].
      pose proof (proj1 (Hcomp C HC)) as HCf. rewrite EC in HCf.
      rewrite EC, (proj1 (candidate_reference env p c gm nn q Hq)).
      rewrite EC in HvC. cbn [vars_in] in HvC. apply andb_true_iff in HvC. destruct HvC as [Hq' _].
      unfold param_eqb in Hq'. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hq'. cbn [orb] in Hq'. unfold bound_b in Hq'.
      destruct (lookup_binding b q) as [ab|] eqn:Ea; [|discriminate Hq'].
      destruct (Hpb q ab Ea) as [_ [o [y [-> _]]]].
      rewrite (free_variable_any b Hpb gm nn q [] o y Ea).
      destruct (Hext0 b Hsb q o y Ea) as [Hy [st [Hl Hfit]]].
      destruct (HQ nn q Ew) as [HVq [Hann Ham]].
      pose proof (HVq o y Hy (fun st' Hl' => ltac:(rewrite Hl in Hl'; injection Hl' as <-; exact Hfit))) as Hay.
      destruct (compfrag_cases env _ HCf) as [Hif|[gm' [nn' [q'' [Eq' [Hsq _]]]]]].
      { (* a plain type variable: the type it is bound to *)
        unfold ifrag in Hif. destruct gm, nn; cbn [no_generics] in Hif; rewrite ?andb_false_r in Hif; try discriminate Hif. exact Hay. }
      injection Eq' as <- <- <-.
      apply (reference_below gm nn q a y Ha Hy Hsq); [|intros En E; rewrite (Hann En) in E; discriminate E|exact Hay].
      (* the common mutability is no more than that given to it *)
      intros m Em. apply (mutability_subtype_trans _ _ _ Ham). pose proof (Hunif C HC) as Hu. fold m0 in Hu. rewrite <- Hu, EC.
      exact (compfrag_given env wf gm nn q m HCf Em).
Qed.

Lemma gstatic_whole: forall (W: VariableStates -> Prop), (forall s t, W s -> capturable t s = None) ->
    forall n p S c s s', (forall k, k < n -> forall b, mleaf b W k) -> gstatic_form p S ->
    of_fragment c -> bottom_only c = true -> Qb c -> W s ->
    unify env n (with_candidate env p c S) c (Ongoing s) = Some (Ongoing s') ->
    W s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (is_nullable env S = false -> is_nullable env c = false)
    /\ forall b, plain_values b -> (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
        nonnull_values b ->
        owners_free b c -> vars_in (fun q => param_eqb q p || bound_b b q) S = true -> gsatisfies b s' ->
        forall C, In C (bound_components S) -> below c (instantiate_free env b (with_candidate env p c C)).
Proof.
    intros W HW n p S c s s' Hleaf [Hcomp Hinter] Hc Hbc Hqc Hs H.
    assert (Hyc: forall b, owners_free b c -> yfrag b c)
        by (intros b Hob; split; [exact Hc|]; split; [exact Hbc|]; split; [exact Hob|exact Hqc]).
    pose proof (of_fragment_no_vars c Hc) as Hnc.
    assert (Hcases: bound_components S = [S] \/ (exists cs, S = Intersection cs) \/ (exists cs, S = Nullable (Intersection cs)))
        by (destruct S as [m c' args|[| | | | | |cs]|g|me msg|v o x|g|cs];
            first [left; reflexivity|right; left; exists cs; reflexivity|right; right; exists cs; reflexivity]).
    destruct Hcases as [E|[[cs ->]|[cs ->]]].
    { rewrite E in Hcomp |- *. destruct (Hcomp S (or_introl eq_refl)) as [HSp [HSo HStop]].
      destruct (pfrag_cases env S HSp) as [HSi|[[gm [nn [q [ES _]]]]|[gm [nn [q [ES _]]]]]].
      - (* no intersection: as any other type of the parameters *)
        pose proof (fun g Eg => HStop g (or_introl Eg)) as HStop'.
        destruct (proj1 (mixed_arguments [] plain_nil bf_nil W HW n (fun k Hk => Hleaf k Hk []))
            _ c s s' (mfrag_candidate [] p c (Hyc [] (owners_free_nil c)) nonnull_nil S HSi HSo HStop') (Hyc [] (owners_free_nil c)) Hs H)
            as [Hs' [Hn' _]].
        split; [exact Hs'|]. split; [exact Hn'|].
        split; [intros HnS; exact (ifrag_candidate_not_nullable n p c S c s s' HSi HStop' (proj1 Hc) HnS H)|].
        intros b Hpb Hbf Hnv Hob Hvb Hsb C [<-|[]].
        destruct (proj1 (mixed_arguments b Hpb Hbf W HW n (fun k Hk => Hleaf k Hk b))
            _ c s s' (mfrag_candidate b p c (Hyc b Hob) Hnv S HSi HSo HStop') (Hyc b Hob) Hs H) as [_ [_ Hsnd]].
        exact (Hsnd Hsb (mbinds_candidate b p c S Hvb Hnc)).
      - (* a type variable of a mutability given to it, narrowed or not: as the type of a parameter *)
        pose proof (HStop _ (or_introl ES)) as Hq. cbn [param_of] in Hq.
        assert (Ew: with_candidate env p c S = S) by (rewrite ES; exact (proj1 (candidate_reference env p c gm nn q Hq))).
        rewrite Ew in H.
        destruct (mixed_parameter [] plain_nil bf_nil W HW n (fun k Hk => Hleaf k Hk []) S c s s' HSp (proj1 (bplain_parts p S HSo)) (proj1 (proj2 (bplain_parts p S HSo))) nonnull_nil
            (Hyc [] (owners_free_nil c)) Hs H) as [Hs' [Hn' _]].
        split; [exact Hs'|]. split; [exact Hn'|].
        split; [intros HnS; rewrite ES in HnS, H; exact (variable_takes_not_nullable n gm nn q c s s' (proj1 Hc) H HnS)|].
        intros b Hpb Hbf Hnv Hob Hvb Hsb C [<-|[]]. rewrite Ew.
        destruct (mixed_parameter b Hpb Hbf W HW n (fun k Hk => Hleaf k Hk b) S c s s' HSp (proj1 (bplain_parts p S HSo)) (proj1 (proj2 (bplain_parts p S HSo))) Hnv (Hyc b Hob) Hs H) as [_ [_ Hsnd]].
        pose proof (mbinds_candidate b p c S Hvb Hnc) as Hm. rewrite Ew in Hm. exact (Hsnd Hsb Hm).
      - (* made nullable *)
        pose proof (HStop _ (or_intror ES)) as Hq. cbn [param_of] in Hq.
        assert (Ew: with_candidate env p c S = S) by (rewrite ES; exact (proj2 (candidate_reference env p c gm nn q Hq))).
        rewrite Ew in H.
        destruct (mixed_parameter [] plain_nil bf_nil W HW n (fun k Hk => Hleaf k Hk []) S c s s' HSp (proj1 (bplain_parts p S HSo)) (proj1 (proj2 (bplain_parts p S HSo))) nonnull_nil
            (Hyc [] (owners_free_nil c)) Hs H) as [Hs' [Hn' _]].
        split; [exact Hs'|]. split; [exact Hn'|].
        split; [intros HnS; rewrite ES in HnS; simpl in HnS; discriminate HnS|].
        intros b Hpb Hbf Hnv Hob Hvb Hsb C [<-|[]]. rewrite Ew.
        destruct (mixed_parameter b Hpb Hbf W HW n (fun k Hk => Hleaf k Hk b) S c s s' HSp (proj1 (bplain_parts p S HSo)) (proj1 (proj2 (bplain_parts p S HSo))) Hnv (Hyc b Hob) Hs H) as [_ [_ Hsnd]].
        pose proof (mbinds_candidate b p c S Hvb Hnc) as Hm. rewrite Ew in Hm. exact (Hsnd Hsb Hm). }
    { destruct (Hinter cs eq_refl) as [Hif [Hcs Hunif]]. cbn [bound_components] in Hcomp, Hif |- *.
      assert (Hcomp': forall C, In C cs -> compfrag env C = true /\ bplain p C = true /\ forall g, C = TypeVariable g -> param_of g <> p).
      { intros C HC. destruct (Hcomp C HC) as [_ [HCo HCt]]. split; [exact (Hif C HC)|]. split; [exact HCo|].
        intros g Eg. exact (HCt g (or_introl Eg)). }
      destruct (gstatic_components W HW n p cs c c s s' Hleaf Hcomp' Hcs Hunif Hc Hbc Hqc Hyc Hs H) as [H1 [H2 [H3 H4]]].
      split; [exact H1|]. split; [exact H2|]. split; [intros _; exact H3|exact H4]. }
    (* a nullable intersection: of the candidate without null, the components made nullable *)
    destruct (Hinter cs eq_refl) as [Hif [Hcs Hunif]]. cbn [bound_components] in Hcomp |- *.
    assert (Hcomp': forall C, In C cs -> compfrag env C = true /\ bplain p C = true /\ forall g, C = TypeVariable g -> param_of g <> p).
    { intros C HC. destruct (Hcomp _ (in_map Nullable _ _ HC)) as [_ [HCo HCt]]. split; [exact (Hif C HC)|]. split; [exact (bplain_nullable p C HCo)|].
      intros g Eg. apply (HCt g). right. rewrite Eg. reflexivity. }
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hshape]. rewrite length_map in Hlen.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q []) /\ q <> p))
        by (intros C HC; exact (static_component_cases env wf p cs C Hif Hcs (fun g Hg => proj2 (proj2 (Hcomp' _ Hg)) g eq_refl) HC)).
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hshape _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q [-> _]]]]]; [reflexivity|exact Hsh]. }
    change (with_candidate env p c (Nullable (Intersection cs))) with (rewrap_nullable (with_candidate env p c (Intersection cs))) in H.
    rewrite (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H. cbn [rewrap_nullable] in H.
    destruct n as [|n]; [discriminate H|].
    rewrite (nullable_target n _ c s (proj1 Hc)) in H. rewrite <- (with_candidate_intersection env p c cs Hlen Hcase Hnull) in H.
    destruct (gstatic_components W HW n p cs c (nullable_assignee c) s s' (fun k Hk => Hleaf k ltac:(lia))
        Hcomp' Hcs Hunif Hc Hbc Hqc (fun b Hob => yfrag_nullable_assignee b c (Hyc b Hob)) Hs H)
        as [Hs' [Hn' [_ Hall]]].
    split; [exact Hs'|]. split; [exact Hn'|]. split; [intros E; simpl in E; discriminate E|].
    intros b Hpb Hbf Hnv Hob Hvb Hsb C' HC'. apply in_map_iff in HC'. destruct HC' as [C [<- HC]].
    destruct (Hcomp' C HC) as [HCf [HCo HCt]].
    pose proof (Hall b Hpb Hbf Hnv Hob Hvb Hsb C HC) as Hb.
    assert (HvC: vars_in (fun q => param_eqb q p || bound_b b q) C = true)
        by (cbn [vars_in] in Hvb; rewrite forallb_forall in Hvb; exact (Hvb C HC)).
    destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q [EC Hq]]]]]; subst C.
    - pose proof (compfrag_ifrag env _ HCf eq_refl) as HCi.
      pose proof (mixed_of_fragment b Hpb Hbf _ (mfrag_candidate b p c (Hyc b Hob) Hnv _ HCi HCo HCt) (mbinds_candidate b p c _ HvC Hnc)) as Hf.
      change (with_candidate env p c (Nullable (RootResolved m cl args))) with (rewrap_nullable (with_candidate env p c (RootResolved m cl args))).
      rewrite (free_rewrap env b). exact (nullable_variable_below false c _ (proj1 Hc) (proj1 Hf) Hb).
    - (* a type variable, narrowed or not, made nullable: the type it is bound to *)
      rewrite (proj2 (candidate_reference env p c gm nn q Hq)). rewrite (proj1 (candidate_reference env p c gm nn q Hq)) in Hb.
      change (instantiate_free env b (Nullable (TypeVariable (mkGenericRef gm nn q []))))
          with (rewrap_nullable (instantiate_free env b (TypeVariable (mkGenericRef gm nn q [])))).
      cbn [vars_in] in HvC. apply andb_true_iff in HvC. destruct HvC as [Hq' _].
      unfold param_eqb in Hq'. rewrite (proj2 (Nat.eqb_neq q p) Hq) in Hq'. cbn [orb] in Hq'. unfold bound_b in Hq'.
      destruct (lookup_binding b q) as [ab|] eqn:Ea; [|discriminate Hq'].
      destruct (Hpb q ab Ea) as [_ [o [y [-> _]]]].
      rewrite (free_variable_any b Hpb gm nn q [] o y Ea) in Hb |- *.
      exact (nullable_variable_below false c _ (proj1 Hc) (proj1 (ref_apply_of_fragment gm nn y (Hbf q o y Ea))) Hb).
Qed.

(*
 * What unify does with a type variable, for the states of generic code: as gtarget_leaf and
 * gassignee_leaf, where the static upper bounds may have type variables. A new lower bound is checked
 * against the static upper bound (mixed_arguments, at a lower fuel); that check, with no bindings at
 * all, keeps the states as they work, and with the bindings that satisfy them it is sound.
 *)
Lemma gleaf_all: forall n b, mleaf b gwf2 n.
Proof.
    induction n as [n IHn] using lt_wf_ind. intros b0. split.
    - (* the variable is the target *)
      intros p bnd A s s' Hs HA H.
      pose proof (variable_target_step n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
      unfold plus_supertype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
      destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
      destruct (is_exact st) eqn:Ee.
      + (* bound exactly: its binding takes A *)
        destruct (keeps_free env wf n _ A s s' Hnl (of_fragment_no_vars A (proj1 HA)) H') as [-> _]. split; [exact Hs|]. split; [auto|].
        intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
        destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hlo in H'.
        exact (proj2 (gwrite_leaf n vb ob X o x A s s K HX Hx (proj1 HA) (proj1 (proj2 HA)) Hc H')).
      + (* between bounds: the lower bound becomes the closest common supertype with A, checked *)
        cbn zeta in H'.
        destruct (He eq_refl) as [Hcap [Hlu [Hbu [Hbl [Hqu [Hql [Hbo Hok]]]]]]].
        pose proof (supertype_of_fragment _ _ Hbl (proj1 HA)) as Hfs.
        destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
            as [[ns|]|] eqn:E; try discriminate H'.
        destruct (keeps_free env wf n _ _ s ns Hnu (of_fragment_no_vars _ Hfs) E) as [-> H0].
        destruct (below_supertype _ _ Hbl (proj1 HA)) as [Hlo HAs].
        pose proof (Qb_supertype _ _ Hbl (proj1 HA) Hql (proj2 (proj2 (proj2 HA)))) as Hqc.
        pose proof (supertype_bottom_only _ _ Hbl (proj1 HA) Hbo (proj1 (proj2 HA))) as Hbc.
        set (c := closest_common_supertype_with env (lower_bound st) A) in *.
        pose proof (of_fragment_no_vars c Hfs) as Hnc.
        set (st' := mkVariableState (static_upper_bound st) (upper_bound st) c false (is_capturable st)).
        assert (Hfit': forall o x, of_fragment x -> gfits st' o x -> gfits st o x).
        { intros o x Hx Hfit. unfold gfits in Hfit |- *. rewrite Ee. unfold st' in Hfit. cbn [is_exact upper_bound lower_bound] in Hfit.
          destruct Hfit as [E1 E2]. split; [|exact E2]. exact (below_trans _ _ x Hbl Hfs Hx Hlo E1). }
        destruct (plus_static_check env (unify env n) st p c (Ongoing s)) as [[s2|]|] eqn:E2; cbn beta iota in H'; try discriminate H'.
        injection H' as <-.
        assert (Hcheck: gwf2 s2 /\ (forall b', gsatisfies b' s2 -> gsatisfies b' s) /\ lookup_state s2 p = Some st
            /\ (no_vars (static_upper_bound st) = false ->
                (is_nullable env (static_upper_bound st) = false -> is_nullable env c = false)
                /\ forall b, plain_values b -> (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x) ->
                    nonnull_values b -> owners_free b c -> vars_in (fun q => param_eqb q p || bound_b b q) (static_upper_bound st) = true ->
                    gsatisfies b s2 -> forall C, In C (bound_components (static_upper_bound st)) ->
                    below c (instantiate_free env b (with_candidate env p c C)))).
        { unfold plus_static_check in E2. destruct (no_vars (static_upper_bound st)) eqn:Ens.
          - injection E2 as <-. split; [exact Hs|]. split; [auto|]. split; [exact Hl|]. intros E'; discriminate E'.
          - unfold gstatic_ok in Hok. rewrite Ens in Hok. destruct Hok as [Hform _].
            destruct (gstatic_whole gwf2 gwf2_capturable n p _ c s s2 IHn Hform Hfs Hbc Hqc Hs E2) as [Hs2 [Hn2 Hsnd]].
            destruct (unify_keeps_from env wf intersect_no_vars supertype_no_vars n (parameter_rank env p) _ c s s2 (gwf2_ranked s Hs)
                (or_intror (conj (candidate_below env wf p c _ Hsv Hnc) Hnc)) E2) as [Kf _].
            split; [exact Hs2|]. split; [exact Hn2|]. split; [rewrite (Kf p (le_n _)); exact Hl|].
            intros _. exact Hsnd. }
        destruct Hcheck as [Hs2 [Hn2 [Hl2 Hchk]]].
        pose proof (gsatisfies_set_state s2 p st st' Hl2 Hfit') as Hn'.
        split; [|split; [intros b Hb; exact (Hn2 b (Hn' b Hb))|]].
        * apply (gwf2_set_state s2 p st' Hs2 Hn'). split; [exact Hnu|]. split; [exact Hnc|]. split; [|exact Hsv].
          intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hbu|]. split; [exact Hfs|].
          split; [exact Hqu|]. split; [exact Hqc|]. split; [exact Hbc|].
          unfold gstatic_ok. unfold st'. cbn [static_upper_bound lower_bound upper_bound].
          unfold gstatic_ok in Hok. destruct (no_vars (static_upper_bound st)) eqn:Ens; [exact Hok|].
          destruct Hok as [Hform _]. split; [exact Hform|].
          intros _. split; [exact (proj1 (Hchk eq_refl))|].
          intros b Hpb' Hbf' Hnv Hob Hvb Hsb. exact (proj2 (Hchk eq_refl) b Hpb' Hbf' Hnv Hob Hvb (Hn' b Hsb)).
        * intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s2 p _)). unfold gfits in Hfit. unfold st' in Hfit.
          cbn [is_exact lower_bound] in Hfit. destruct Hfit as [E1 _]. exact (below_trans _ _ x (proj1 HA) Hfs Hx HAs E1).
    - (* the variable is the assignee *)
      intros p bnd A s s' Hs HA H.
      pose proof (variable_assignee_step n p bnd A s s' (proj1 (proj1 HA)) H) as H'.
      unfold plus_subtype_constraint in H'. destruct (lookup_state s p) as [st|] eqn:Hl; [|discriminate H'].
      destruct (Hs p st Hl) as [Hnu [Hnl [He Hsv]]].
      destruct (is_exact st) eqn:Ee.
      + (* bound exactly: A takes what its binding gives *)
        destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars A (proj1 HA)) Hnu H') as [-> _]. split; [exact Hs|]. split; [auto|].
        intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
        destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hu in H'.
        exact (proj2 (gread_leaf n vb ob X o x A s s K HX Hx (proj1 HA) Hc H')).
      + (* between bounds: the upper bound becomes the intersection with A *)
        cbn zeta in H'.
        destruct (He eq_refl) as [Hcap [Hlu [Hbu [Hbl [Hqu [Hql [Hbo Hok]]]]]]].
        pose proof (intersect_of_fragment _ _ Hbu (proj1 HA)) as Hfi.
        destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
        destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s))
            as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
        destruct (keeps_free env wf n _ _ s ns (of_fragment_no_vars _ Hfi) Hnl E) as [-> H0].
        destruct (intersect_below_both _ _ Hbu (proj1 HA)) as [Hiu HiA].
        set (st' := mkVariableState (static_upper_bound st) (intersect env (upper_bound st) A) (lower_bound st) false (is_capturable st)).
        assert (Hfit': forall o x, of_fragment x -> gfits st' o x -> gfits st o x).
        { intros o x Hx Hfit. unfold gfits in Hfit |- *. rewrite Ee. unfold st' in Hfit.
          cbn [is_exact upper_bound lower_bound] in Hfit. destruct Hfit as [E1 E2]. split; [exact E1|].
          exact (below_trans x _ _ Hx Hfi Hbu E2 Hiu). }
        pose proof (gsatisfies_set_state s p st st' Hl Hfit') as Hn'.
        split; [|split; [exact Hn'|]].
        * apply (gwf2_set_state s p st' Hs Hn'). split; [exact (of_fragment_no_vars _ Hfi)|]. split; [exact Hnl|]. split; [|exact Hsv].
          intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hfi|]. split; [exact Hbl|].
          split; [exact (Qb_intersect _ _ Hbu (proj1 HA) Hqu (proj2 (proj2 (proj2 HA))))|]. split; [exact Hql|]. split; [exact Hbo|].
          unfold gstatic_ok. unfold st'. cbn [static_upper_bound lower_bound upper_bound].
          unfold gstatic_ok in Hok. destruct (no_vars (static_upper_bound st)) eqn:Ens.
          -- intros x Hx Ex. exact (Hok x Hx (below_trans x _ _ Hx Hfi Hbu Ex Hiu)).
          -- destruct Hok as [Hform Hchk]. split; [exact Hform|].
             intros Hnn. split; [exact (proj1 (Hchk Hnn))|].
             intros b Hpb' Hbf' Hnv Hob Hvb Hsb. exact (proj2 (Hchk Hnn) b Hpb' Hbf' Hnv Hob Hvb (Hn' b Hsb)).
        * intros o x Hx Hfit. specialize (Hfit _ (lookup_set_same s p _)). unfold gfits in Hfit. unfold st' in Hfit.
          cbn [is_exact upper_bound] in Hfit. destruct Hfit as [_ E2]. exact (below_trans x _ _ Hx Hfi (proj1 HA) E2 HiA).
Qed.

(* The final value of a variable that isn't bound exactly: of the fragment, within its bounds *)
Lemma gfinal_value_fits: forall s p st o, gwf2 s -> lookup_state s p = Some st -> is_exact st = false ->
    of_fragment (Constraints.final_value env st) /\ gfits st o (Constraints.final_value env st).
Proof.
    intros s p st o Hs Hl He. destruct (Hs p st Hl) as [_ [_ [Hb _]]]. destruct (Hb He) as [_ [Hlu [Hfu [Hfl _]]]].
    unfold gfits. rewrite He. unfold Constraints.final_value.
    destruct (is_non_nullable_nothing env (lower_bound st)).
    - split; [exact Hfu|]. split; [exact Hlu|exact (below_refl _ Hfu)].
    - split; [exact Hfl|]. split; [exact (below_refl _ Hfl)|exact Hlu].
Qed.

(* The final value of a type parameter of a non-null bound isn't nullable: below the bound, where it
   has no type variables; where it has, the lower bound, checked against it *)
Lemma gfinal_not_nullable: forall s p st, gwf2 s -> lookup_state s p = Some st -> is_exact st = false ->
    to_generic (static_upper_bound st) = parameter_bound env p ->
    (no_vars (static_upper_bound st) = true -> of_fragment (static_upper_bound st)) ->
    (no_vars (static_upper_bound st) = false -> is_non_nullable_nothing env (lower_bound st) = false) ->
    is_nullable env (Generic (mkGenericRef None false p [])) = false ->
    is_nullable env (Constraints.final_value env st) = false.
Proof.
    intros s p st Hs Hl He ES Hcl Hlow Hn.
    destruct (gfinal_value_fits s p st ref Hs Hl He) as [Hf Hfit].
    destruct (Hs p st Hl) as [_ [_ [Hb _]]]. destruct (Hb He) as [_ [_ [_ [_ [_ [_ [_ Hok]]]]]]].
    unfold gstatic_ok in Hok. destruct (no_vars (static_upper_bound st)) eqn:Ens.
    - unfold gfits in Hfit. rewrite He in Hfit. destruct Hfit as [_ Hup]. pose proof (Hcl eq_refl) as HfS.
      exact (within_bound_not_nullable p _ _ ES (proj1 HfS) (proj1 Hf) (Hok _ Hf Hup) Hn).
    - destruct Hok as [_ Hchk]. pose proof (Hlow eq_refl) as Hnn. unfold Constraints.final_value. rewrite Hnn.
      apply (proj1 (Hchk Hnn)).
      rewrite <- is_nullable_to_generic, ES, <- (effective_bound_plain env ranked), <- (is_nullable_generic env ranked). exact Hn.
Qed.

(* The static upper bound S of the type parameter p, one of vars: its declared bound with type
   variables in place of the type parameters; a type of the fragment, as Qb has them, where it has no
   type variables; where it has, a type of the parameters without ownerships of type parameters, a
   type variable of a mutability given to it, narrowed or made nullable among them (pfrag), or an
   intersection, nullable or not, of components of ifrag or type variables (compfrag), assigned
   as one mutability *)
Definition gstatic_bound (vars: list (TypeParameterId * EType)) (p: TypeParameterId) (S: EType): Prop :=
    to_generic S = parameter_bound env p
    /\ vars_in (fun q => static_vars env p q && existsb (param_eqb q) (map fst vars)) S = true
    /\ (no_vars S = true -> of_fragment S /\ Qb S)
    /\ (no_vars S = false -> (forall C, In C (bound_components S) -> pfrag env C = true /\ bplain p C = true)
        /\ forall cs, inter_of S = Some cs -> (forall C, In C cs -> compfrag env C = true)
            /\ components_sfrag env (map to_generic cs) = true
            /\ forall C, In C cs -> assignment_mutability env C = assignment_mutability env (Intersection cs)).

(* A type parameter with a static upper bound starts inference as gwf2 has it *)
Lemma ginitial_ok: forall vars p S s, gstatic_bound vars p S ->
    gstate_ok s p (mkVariableState S (initial_upper_bound S) bottom_type false false).
Proof.
    intros vars p S s [Hg [Hsv [Hcl Hvar]]].
    assert (Hsv': vars_in (static_vars env p) S = true)
        by (apply (vars_in_mono _ _ (fun q E => proj1 (proj1 (andb_true_iff _ _) E)) _ Hsv)).
    pose proof (yfrag_of_fragment [] _ (yfrag_bottom [])) as Hfb. pose proof (yfrag_of_fragment [] _ (yfrag_top [])) as Hft.
    pose proof (proj1 (proj2 (yfrag_bottom []))) as Hbb.
    unfold gstate_ok. cbn [upper_bound lower_bound is_exact is_capturable static_upper_bound].
    destruct (no_vars S) eqn:Ens.
    - destruct (Hcl eq_refl) as [HfS HqS]. rewrite (initial_closed S Ens).
      split; [exact Ens|]. split; [reflexivity|]. split; [|exact Hsv'].
      intros _. split; [reflexivity|]. split; [exact (below_bottom S HfS)|]. split; [exact HfS|]. split; [exact Hfb|].
      split; [exact HqS|]. split; [exact Qb_bottom|]. split; [exact Hbb|]. unfold gstatic_ok. cbn [static_upper_bound upper_bound]. rewrite Ens.
      intros x _ Ex. exact Ex.
    - destruct (Hvar eq_refl) as [Hcomp Hinter]. unfold initial_upper_bound. rewrite Ens.
      split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hsv'].
      intros _. split; [reflexivity|]. split; [exact (below_bottom _ Hft)|]. split; [exact Hft|]. split; [exact Hfb|].
      split; [exact Qb_top|]. split; [exact Qb_bottom|]. split; [exact Hbb|].
      unfold gstatic_ok. cbn [static_upper_bound lower_bound]. rewrite Ens.
      split; [split; [|exact Hinter]|].
      + (* at the top of the bound, components of a lower rank: none is the variable itself *)
        assert (Hr: forall C, In C (bound_components S) -> ranked_below env (parameter_rank env p) (to_generic C) = true).
        { intros C HC. pose proof (wf_bounds_ranked env wf p) as Hrk. rewrite <- Hg in Hrk.
          destruct S as [m c args|[m' c' a'|n'|g''|me' msg'|v' o' x'|g''|cs]|g'|me msg|v o x|g'|cs]; cbn [bound_components] in HC;
              try (destruct HC as [<-|[]]; exact Hrk); cbn [to_generic ranked_below] in Hrk;
              change (forallb (ranked_below env (parameter_rank env p)) (map to_generic cs) = true) in Hrk;
              rewrite forallb_forall in Hrk.
          - apply in_map_iff in HC. destruct HC as [c [<- Hc]]. exact (Hrk _ (in_map to_generic _ _ Hc)).
          - exact (Hrk _ (in_map to_generic _ _ HC)). }
        intros C HC. destruct (Hcomp C HC) as [HCi HCo]. split; [exact HCi|]. split; [exact HCo|].
        intros g EC Ep. pose proof (Hr _ HC) as Hrc. destruct EC as [EC|EC]; subst C;
            (destruct g as [gm nn q vs]; cbn [to_generic ranked_below] in Hrc; unfold rank_of in Hrc; cbn [param_of] in Hrc, Ep;
             apply Nat.ltb_lt in Hrc; subst q; lia).
      + unfold gstatic_checked. cbn [lower_bound]. intros E. change (class_eqb nothing nothing = false) in E.
        rewrite class_eqb_refl in E. discriminate E.
Qed.

(* The final value of the type parameter p *)
Definition gfinal_of (U: VariableStates) (p: TypeParameterId): EType :=
    match lookup_state U p with Some st => Constraints.final_value env st | None => bottom_type end.

(*
 * An invocation in generic code of a function whose type parameters are bounded by types mentioning
 * them, inferred, is sound: where unify accepts each argument for its parameter, in turn, and
 * inference picks a lower bound for each variable whose bound has type variables, the final values
 * are within the static upper bounds, the type variables replaced by them, and each argument fits its
 * parameter, so replaced. The types of the arguments mention the type parameters of the caller, which
 * stay as they are (instantiate_free); none of them is one of the variables (owners_free). Of a type
 * variable of a mutability given to it, or narrowed, the instance is of that mutability, and without
 * null where it is narrowed, as for a type parameter.
 *)
Theorem generic_invocation_with_bounded_variables_sound: forall n vars Ps As U,
    NoDup (map fst vars) ->
    (forall p S, In (p, S) vars -> gstatic_bound vars p S) ->
    (forall P, In P Ps -> qfrag env P = true /\ (forall C, In C (intersected_components P) -> plain_owners C = true)
        /\ vars_in (fun q => existsb (param_eqb q) (map fst vars)) P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (for_inference_of vars []) = Some (Ongoing U) ->
    (forall p S st, In (p, S) vars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of U (fst v)))) vars ->
    (forall A, In A As -> yfrag b A) ->
    (forall t, Qb t -> owners_free b t) ->
    (forall p S, In (p, S) vars -> forall C, In C (bound_components S) -> below (gfinal_of U p) (instantiate_free env b C))
    /\ (forall P A, In (P, A) (combine Ps As) -> below A (instantiate_free env b P)).
Proof.
    intros n vars Ps As U Hnd Hst HPs HPn Hfold Hlow b Hbdef HAs Hown.
    set (s0 := map (fun '(q, bnd) => (q, mkVariableState bnd (initial_upper_bound bnd) bottom_type false (existsb (param_eqb q) []))) vars).
    assert (Hs0: for_inference_of vars [] = Ongoing s0) by reflexivity. rewrite Hs0 in Hfold.
    assert (Hl0: forall p S, In (p, S) vars -> lookup_state s0 p = Some (mkVariableState S (initial_upper_bound S) bottom_type false false)).
    { intros p S Hin. exact (lookup_for_inference vars [] p S Hnd Hin). }
    assert (Hwf0: gwf2 s0).
    { intros p st Hp. destruct (lookup_for_inference_in vars [] p st Hp) as [S Hin].
      rewrite (Hl0 p S Hin) in Hp. injection Hp as <-. exact (ginitial_ok vars p S s0 (Hst p S Hin)). }
    (* the states the fold ends with: with no bindings at all *)
    assert (Hstep0: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf2 s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf2 s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP [HoP _]]. destruct (HAs A HA) as [HfA [HbA [_ HqA]]].
      destruct (mqparameter [] plain_nil bf_nil gwf2 gwf2_capturable n (fun k _ => gleaf_all k [])
          P A s s' HfP HoP (HPn P HP) nonnull_nil (conj HfA (conj HbA (conj (owners_free_nil A) HqA))) Hs E) as [Hs' [Hn' _]].
      split; [exact Hs'|exact Hn']. }
    destruct (mfold_chain gwf2 n _ s0 U Hstep0 Hwf0 Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env n _ s0 U Hfold) as [_ [Hkeep2 _]].
    (* the final values *)
    assert (Hfin: forall p S, In (p, S) vars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ static_upper_bound st = S /\ gfinal_of U p = Constraints.final_value env st
        /\ of_fragment (gfinal_of U p) /\ gfits st ref (gfinal_of U p)).
    { intros p S Hin. destruct (Hkeep2 p _ (Hl0 p S Hin) eq_refl eq_refl) as [st [Hl [He [_ Hs]]]].
      destruct (gfinal_value_fits U p st ref HwfU Hl He) as [Hf Hfit].
      assert (Ef: gfinal_of U p = Constraints.final_value env st) by (unfold gfinal_of; rewrite Hl; reflexivity).
      exists st. split; [exact Hl|]. split; [exact He|]. split; [exact Hs|]. split; [exact Ef|]. rewrite Ef. split; [exact Hf|exact Hfit]. }
    assert (Hlb: forall p S, In (p, S) vars -> lookup_binding b p = Some (TypeArgument Model.invariant ref (gfinal_of U p))).
    { intros p S Hin. rewrite Hbdef. exact (lookup_map_vars vars (fun v => TypeArgument Model.invariant ref (gfinal_of U (fst v))) p S Hnd Hin). }
    assert (Hlb_in: forall q a, lookup_binding b q = Some a -> exists S, In (q, S) vars /\ a = TypeArgument Model.invariant ref (gfinal_of U q)).
    { intros q a Eq. rewrite Hbdef in Eq. destruct (lookup_own vars (fun q => TypeArgument Model.invariant ref (gfinal_of U q)) q a Eq) as [Ea Hq].
      apply in_map_iff in Hq. destruct Hq as [[q1 S] [Hfst Hin]]. simpl in Hfst. subst q1. exists S. split; [exact Hin|exact Ea]. }
    assert (Hpb: plain_values b).
    { intros q a Eq. destruct (Hlb_in q a Eq) as [S [Hin ->]]. split; [reflexivity|].
      destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf _]]]]]].
      exists ref, (gfinal_of U q). split; [reflexivity|exact (gfrag_not_nested env _ (proj1 Hf))]. }
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x).
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [S [Hin Ea]]. injection Ea as -> ->.
      destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf _]]]]]]. exact Hf. }
    assert (Hsat: gsatisfies b U).
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [S [Hin Ea]]. injection Ea as -> ->.
      destruct (Hfin q S Hin) as [st [Hl [_ [_ [_ [Hf Hfit]]]]]]. split; [exact Hf|]. exists st. split; [exact Hl|exact Hfit]. }
    assert (Hbound: forall t, vars_in (fun q => existsb (param_eqb q) (map fst vars)) t = true -> vars_in (bound_b b) t = true).
    { apply vars_in_mono. intros q E. apply existsb_exists in E. destruct E as [q' [Hq' Eq]]. apply param_eqb_eq in Eq. subst q'.
      apply in_map_iff in Hq'. destruct Hq' as [[q1 S] [Hfst Hin]]. simpl in Hfst. subst q1. unfold bound_b. rewrite (Hlb q S Hin). reflexivity. }
    (* the values of non-null bounds aren't null: the final values, within the bounds *)
    assert (Hnv: nonnull_values b).
    { intros q o x Eq Hnq. destruct (Hlb_in q _ Eq) as [S [Hin Ea]]. injection Ea as _ ->.
      destruct (Hfin q S Hin) as [st [Hl [He [Hs [Ef _]]]]]. destruct (Hst q S Hin) as [ES [_ [Hcl _]]]. subst S.
      rewrite Ef. exact (gfinal_not_nullable U q st HwfU Hl He ES (fun E => proj1 (Hcl E)) (fun E => Hlow q _ st Hin E Hl) Hnq). }
    (* the final values, within the static upper bounds *)
    assert (Hfinals: forall p S, In (p, S) vars -> forall C, In C (bound_components S) ->
        below (gfinal_of U p) (instantiate_free env b C)).
    { intros p S Hin C HC. destruct (Hfin p S Hin) as [st [Hl [He [Hs [Ef [Hf Hfit]]]]]].
      destruct (Hst p S Hin) as [_ [Hsv [Hcl _]]].
      destruct (HwfU p st Hl) as [_ [_ [Hw _]]]. destruct (Hw He) as [_ [_ [_ [_ [_ [_ [_ Hok]]]]]]].
      unfold gstatic_ok in Hok. rewrite Hs in Hok. destruct (no_vars S) eqn:Ens.
      + (* without type variables: below the upper bound, which is below it, and its components *)
        destruct (Hcl eq_refl) as [HfS HqS]. unfold gfits in Hfit. rewrite He in Hfit. destruct Hfit as [_ Hup].
        destruct (bound_component_of S C HfS HqS HC) as [HfC [HqC HSC]].
        rewrite (free_unmentioned env b Hpb C (proj1 HfC) (unmentioned b C (proj1 HfC) (Hown C HqC))).
        exact (below_trans _ S C Hf HfS HfC (Hok _ Hf Hup) HSC).
      + (* with them: the lower bound, checked against it *)
        destruct Hok as [[Hcomp _] Hchk]. destruct (Hcomp C HC) as [HCp [HCo HCt]].
        pose proof (Hlow p S st Hin Ens Hl) as Hnn.
        assert (Exl: gfinal_of U p = lower_bound st) by (rewrite Ef; unfold Constraints.final_value; rewrite Hnn; reflexivity).
        destruct (HwfU p st Hl) as [_ [_ [Hw' _]]]. destruct (Hw' He) as [_ [_ [_ [Hfl [_ [Hql _]]]]]].
        unfold gstatic_checked in Hchk. rewrite Hs in Hchk.
        assert (Hvb: vars_in (fun q => param_eqb q p || bound_b b q) S = true).
        { apply (vars_in_mono (bound_b b)); [intros q E; rewrite E; apply orb_true_r|].
          apply Hbound. apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ Hsv). }
        pose proof (proj2 (Hchk Hnn) b Hpb Hbf Hnv (Hown _ Hql) Hvb Hsat C HC) as Hc.
        rewrite Exl. destruct (ifrag env C) eqn:HCi.
        *
          rewrite (free_candidate env b p (lower_bound st) C Hpb (proj1 Hfl) (unmentioned b _ (proj1 Hfl) (Hown _ Hql))
              (ifrag_plain_variables p C HCi HCo)) in Hc.
          rewrite (free_ext env _ b (with_value_same b p (lower_bound st) ltac:(rewrite (Hlb p S Hin), Exl; reflexivity)) C) in Hc.
          exact Hc.
        * (* a type variable of a mutability given to it, narrowed or made nullable, other than p *)
          destruct (pfrag_cases env C HCp) as [H|[[gm [nn [q [EC _]]]]|[gm [nn [q [EC _]]]]]]; [rewrite H in HCi; discriminate HCi| |];
              subst C; [rewrite (proj1 (candidate_reference env p _ gm nn q (HCt _ (or_introl eq_refl)))) in Hc
                       |rewrite (proj2 (candidate_reference env p _ gm nn q (HCt _ (or_intror eq_refl)))) in Hc]; exact Hc. }
    split; [exact Hfinals|].
    - (* the arguments: with the bindings *)
      assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf2 s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
          gwf2 s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (instantiate_free env b P))).
      { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
        destruct (HPs P HP) as [HfP [HoP HvP]].
        destruct (mqparameter b Hpb Hbf gwf2 gwf2_capturable n (fun k _ => gleaf_all k b)
            P A s s' HfP HoP (HPn P HP) Hnv (HAs A HA) Hs E) as [Hs' [Hn' Hsnd]].
        split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb. exact (Hsnd Hsb (Hbound P HvP)). }
      destruct (mfold_chain gwf2 n _ s0 U (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
          Hwf0 Hfold) as [_ [_ Hall]].
      intros P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
      exact (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hsat)).
Qed.

End GenericStatic.

(* ---------------------------------------------------------------------------------------------- *)
(* Intersections as the types of parameters                                                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section ParameterIntersections.

Variable b: Bindings.
Variable K: nat.
Hypothesis Hnv: nonnull_values b.

(* An intersection as the type of a parameter, of the argument A: whatever bindings satisfy the states
   unify ends with, A is below the instance of each component, as for a static upper bound
   (gstatic_components), the components as they are; and A is non-null *)
Lemma gparam_components: forall n cs A s s', (forall C, In C cs -> compfrag env C = true) ->
    components_sfrag env (map to_generic cs) = true -> (forall C, In C cs -> args_narrowed env C = true) ->
    yfrag b A -> bound_in env b K [] (Intersection (map to_generic cs)) = true -> gwf_states s ->
    unify env n (Intersection cs) A (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ is_nullable env A = false
    /\ (gsatisfies b s' -> forall C, In C cs -> below A (inst env b C)).
Proof.
    intros n cs A s s' HSi Hcs Hcn HA Hb Hs H.
    assert (Hcase: forall C, In C cs -> (exists m cl args, C = RootResolved m cl args)
        \/ (exists gm nn q, C = TypeVariable (mkGenericRef gm nn q [])))
        by (intros C HC; exact (param_component_cases env wf cs C HSi Hcs HC)).
    assert (HbC: forall C, In C cs -> bound_in env b K [] (to_generic C) = true)
        by (intros C HC; exact (bound_in_component env b K [] _ _ Hb (in_map _ _ _ HC))).
    destruct (components_sfrag_facts env _ Hcs) as [Hlen Hcsf]. rewrite length_map in Hlen.
    assert (Hnull: forall C, In C cs -> is_nullable env C = false).
    { intros C HC. destruct (Hcsf _ (in_map to_generic _ _ HC)) as [Hsh _]. unfold is_component_shape in Hsh.
      apply andb_true_iff in Hsh. destruct Hsh as [_ Hsh]. apply negb_true_iff in Hsh.
      destruct (Hcase C HC) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [reflexivity|exact Hsh]. }
    pose proof HA as [Ha [Hba [Hoa Hqa]]].
    assert (Haa: assignee_mutability env A = assignment_mutability env A)
        by (destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; reflexivity).
    destruct n as [|n1]; [discriminate H|].
    assert (Hshape: match A with Nullable _ | TypeVariable _ | Error _ _ => False | _ => True end \/ exists an, A = Nullable an).
    { destruct (gfrag_cases env A (proj1 Ha)) as [[? [? [? ->]]]|[[an [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]];
          [left; exact I|right; eauto|left; exact I|left; exact I]. }
    destruct Hshape as [Hshape|[an Ean]].
    2:{ (* a nullable argument, for a non-null intersection *)
        assert (Hin: is_nullable env (Intersection cs) = false).
        { destruct cs as [|C0 cs0]; [simpl in Hlen; lia|].
          exact (intersection_not_nullable env (C0 :: cs0) C0 (or_introl eq_refl) (Hnull C0 (or_introl eq_refl))). }
        subst A. rewrite (unify_not_nullable_intersection env n1 cs _ s Hin) in H. discriminate H. }
    rewrite unify_step_once in H. unfold unify_step in H. cbn beta iota in H.
    rewrite (unify_intersection_body _ _ _ A s Hshape) in H. unfold intersection_body in H. cbv zeta in H.
    set (ns := filter (fun x => negb (is_type_variable x)) cs) in H.
    set (vs := filter is_type_variable cs) in H.
    (* the components that aren't type variables: types of the parameters *)
    assert (Hns: forall x, In x ns -> forall s0 s0', gwf_states s0 -> unify env n1 x A (Ongoing s0) = Some (Ongoing s0') ->
        gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ (gsatisfies b s0' -> below A (inst env b x))).
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv]. apply negb_true_iff in Hv.
      exact (proj1 (generic_arguments b K Hnv n1) x A s0 s0' (compfrag_ifrag env x (HSi x Hx) Hv) (Hcn x Hx) HA (HbC x Hx) Hs0 E0). }
    destruct (fold_unify (fun inner component => unify env n1 component A inner) ns (Ongoing s)) as [[s2|]|] eqn:E2;
        cbn beta iota in H; try discriminate H.
    destruct (gfold_list gwf_states (fun x inner => unify env n1 x A inner) ns s s2 (fun x => unify_keeps_failure env n1 x A)
        (fun x s0 s0' Hx Hs0 E0 => let H' := Hns x Hx s0 s0' Hs0 E0 in conj (proj1 H') (proj1 (proj2 H'))) Hs E2) as [Hs2 [Hn2 Hall2]].
    (* what the type variables among the components take *)
    assert (Hmid: exists na s3, gwf_states s3 /\ (forall b', gsatisfies b' s3 -> gsatisfies b' s2)
        /\ yfrag b na /\ below A na /\ (na = A \/ is_nullable env A = false)
        /\ is_subtype_of (assignee_mutability env A) (assignee_mutability env na) = true
        /\ fold_unify (fun inner component =>
            match unify env n1 component na inner with
            | Some Failed => unify env n1 component A inner
            | r => r
            end) vs (Ongoing s3) = Some (Ongoing s')).
    { destruct (find_first (fun component => unify env n1 component A (Ongoing s2)) ns) as [[[cov s3]|]|] eqn:E3;
          cbn beta iota in H; [| |discriminate H].
      - (* covered: the variables take Any of the mutability of A, as far as the covering component allows *)
        destruct (find_first_found _ _ _ _ E3) as [Hcov Ecov].
        destruct (Hns cov Hcov s2 s3 Hs2 Ecov) as [Hs3 [Hn3 _]].
        apply filter_In in Hcov. destruct Hcov as [Hcov Hv]. apply negb_true_iff in Hv.
        destruct (Hcase cov Hcov) as [[mc [cl1 [argsc ->]]]|[gm [nn [q ->]]]]; [|discriminate Hv].
        destruct (root_takes n1 mc cl1 argsc A s2 s3 (proj1 Ha) Ecov) as [Hcn' Hcm].
        rewrite Hcn', andb_false_r in H.
        set (m' := intersect_mutability (mutability_of env A) (mutability_of env (RootResolved mc cl1 argsc))) in H.
        assert (Hm': is_subtype_of (assignment_mutability env A) m' = true).
        { unfold m'. apply intersect_mutability_greatest.
          + exact (assignment_mutability_below env ranked A).
          + exact (mutability_subtype_trans _ _ _ Hcm (assignment_mutability_below env ranked _)). }
        exists (RootResolved (Some m') any []), s3.
        split; [exact Hs3|]. split; [exact Hn3|].
        split; [split; [exact (any_of_fragment m')|]|].
        { split; [cbn [bottom_only]; unfold class_eqb; destruct (Class_eq_dec any nothing) as [E|_]; [discriminate E|reflexivity]|].
          split; [exact I|exact (Qb_any m')]. }
        split; [exact (below_any_of _ _ Ha Hcn' Hm')|]. split; [right; exact Hcn'|].
        split; [|exact H]. rewrite Haa. cbn [assignee_mutability assignment_mutability or_readonly].
        rewrite (wf_any_is_not_const env wf). exact Hm'.
      - (* nothing covers: the variables take A *)
        exists A, s2. split; [exact Hs2|]. split; [auto|]. split; [exact HA|].
        split; [exact (below_refl A Ha)|]. split; [left; reflexivity|]. split; [apply mutability_is_subtype_of_refl|exact H]. }
    destruct Hmid as [na [s3 [Hs3 [Hn3 [Hyna [Hcna [Hnna [Hnam Hfold]]]]]]]].
    set (VSound := fun x u => forall gm nn q, x = TypeVariable (mkGenericRef gm nn q []) ->
        (forall o y, of_fragment y -> (forall st, lookup_state u q = Some st -> gfits st o y) -> below A y)
        /\ is_nullable env A = false
        /\ (forall m, gm = Some m -> is_subtype_of (assignee_mutability env A) m = true)).
    assert (Hvs: forall x, In x vs -> forall s0 s0', gwf_states s0 ->
        match unify env n1 x na (Ongoing s0) with Some Failed => unify env n1 x A (Ongoing s0) | r => r end = Some (Ongoing s0') ->
        gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ VSound x s0').
    { intros x Hx s0 s0' Hs0 E0. apply filter_In in Hx. destruct Hx as [Hx Hv].
      destruct (Hcase x Hx) as [[m [cl [args ->]]]|[gm [nn [q ->]]]]; [discriminate Hv|].
      destruct n1 as [|n2]; [discriminate E0|].
      assert (Hone: forall A0, yfrag b A0 -> (forall y, of_fragment y -> below A0 y -> below A y) -> (A0 = A \/ is_nullable env A = false) ->
          is_subtype_of (assignee_mutability env A) (assignee_mutability env A0) = true ->
          unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) A0 (Ongoing s0) = Some (Ongoing s0') ->
          gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0) /\ VSound (TypeVariable (mkGenericRef gm nn q [])) s0').
      { intros A0 HA0 Hthr HAa HAm EA.
        assert (Hsh: match A0 with Error _ _ | TypeVariable _ => False | _ => True end)
            by (destruct (gfrag_cases env A0 (proj1 (proj1 HA0))) as [[? [? [? ->]]]|[[? [-> _]]|[[? [? [? [? [-> _]]]]]|[? ->]]]]; exact I).
        destruct (unify_variable_given env wf n2 gm nn q A0 s0 s0' Hsh EA) as [EA' [HAg Hnul]].
        destruct (gtarget_leaf n2 q [] A0 s0 s0' Hs0 (proj1 HA0) (proj1 (proj2 HA0)) (proj2 (proj2 (proj2 HA0))) EA')
            as [Hs0' [Hn0 Hsnd]].
        split; [exact Hs0'|]. split; [exact Hn0|].
        intros gm' nn' q' Eq. injection Eq as <- <- <-. split; [intros o y Hy Hfit; exact (Hthr y Hy (Hsnd o y Hy Hfit))|].
        split.
        - (* the component is non-null, so is A *)
          destruct HAa as [->|Ha']; [|exact Ha'].
          destruct (is_nullable env A) eqn:En; [|reflexivity].
          rewrite (Hnull _ Hx) in Hnul. discriminate (Hnul eq_refl).
        - intros m Em. exact (mutability_subtype_trans _ _ _ HAm (HAg m Em)). }
      destruct (unify env (S n2) (TypeVariable (mkGenericRef gm nn q [])) na (Ongoing s0)) as [[u|]|] eqn:Ena; try discriminate E0.
      - cbn beta iota in E0. injection E0 as ->.
        exact (Hone na Hyna (fun y Hy E => below_trans A na y Ha (proj1 Hyna) Hy Hcna E) Hnna Hnam Ena).
      - exact (Hone A HA (fun y _ E => E) (or_introl eq_refl) (mutability_is_subtype_of_refl _) E0). }
    assert (Hgf: forall x, (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        x Failed = Some Failed).
    { intros x. cbn beta. rewrite (unify_keeps_failure env n1 x na). apply unify_keeps_failure. }
    destruct (gfold_list gwf_states (fun x inner => match unify env n1 x na inner with Some Failed => unify env n1 x A inner | r => r end)
        vs s3 s' Hgf (fun x s0 s0' Hx Hs0 E0 => let H' := Hvs x Hx s0 s0' Hs0 E0 in conj (proj1 H') (proj1 (proj2 H'))) Hs3 Hfold)
        as [Hs' [Hn' Hallv]].
    split; [exact Hs'|]. split; [intros b' Hb'; apply Hn2, Hn3, Hn', Hb'|].
    split.
    - (* A is non-null: a component takes it *)
      assert (Hne: exists C1, In C1 cs) by (destruct cs as [|C1 cs']; [simpl in Hlen; lia|exists C1; left; reflexivity]).
      destruct Hne as [C1 HC1]. destruct (Hcase C1 HC1) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      + assert (Hin: In C1 ns) by (apply filter_In; split; [exact HC1|rewrite EC; reflexivity]).
        destruct (Hall2 _ Hin) as [s0 [s0' [_ [E0 _]]]]. rewrite EC in E0.
        exact (proj1 (root_takes n1 m cl args A s0 s0' (proj1 Ha) E0)).
      + assert (Hin: In C1 vs) by (apply filter_In; split; [exact HC1|rewrite EC; reflexivity]).
        destruct (Hallv _ Hin) as [s0 [s0' [Hs0 [E0 _]]]].
        destruct (Hvs _ Hin s0 s0' Hs0 E0) as [_ [_ HQ]]. exact (proj1 (proj2 (HQ gm nn q EC))).
    - intros Hsb C HC. destruct (Hcase C HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      + (* a class type *)
        assert (Hin: In C ns) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
        destruct (Hall2 _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
        exact (proj2 (proj2 (Hns C Hin s0 s0' Hs0 E0)) (Hext0 b (Hn3 b (Hn' b Hsb)))).
      + (* a type variable: the type it is bound to, of the mutability given to it and narrowed or not *)
        assert (Hin: In C vs) by (apply filter_In; split; [exact HC|rewrite EC; reflexivity]).
        destruct (Hallv _ Hin) as [s0 [s0' [Hs0 [E0 Hext0]]]].
        destruct (Hvs _ Hin s0 s0' Hs0 E0) as [_ [_ HQ]].
        destruct (HQ gm nn q EC) as [HVq [HnA Ham]].
        pose proof (HbC C HC) as HbCq. pose proof (HSi C HC) as HCf. rewrite EC in HbCq, HCf.
        destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbCq) as [o [y [Ey _]]]. cbn [param_of] in Ey.
        rewrite EC, (proj1 (inst_reference env b gm nn q [] _ _ _ Ey)).
        destruct (Hext0 b Hsb q o y Ey) as [Hy [st [Hl Hfit]]].
        pose proof (HVq o y Hy (fun st' Hl' => ltac:(rewrite Hl in Hl'; injection Hl' as <-; exact Hfit))) as Hay.
        destruct (compfrag_cases env _ HCf) as [Hif|[gm' [nn' [q'' [Eq' [Hsq _]]]]]].
        { unfold ifrag in Hif. destruct gm, nn; cbn [no_generics] in Hif; rewrite ?andb_false_r in Hif; try discriminate Hif. exact Hay. }
        injection Eq' as <- <- <-.
        exact (reference_below gm nn q A y Ha Hy Hsq Ham (fun _ E => ltac:(rewrite HnA in E; discriminate E)) Hay).
Qed.

(* A parameter of any type of qfrag: what the instance of its type takes; of an intersection, nullable
   or not, as ofComponents makes the instance (below_of_components) *)
Lemma generic_qparameter: forall n P A s s', qfrag env P = true -> args_narrowed env P = true -> yfrag b A ->
    bound_in env b K [] (pgeneric P) = true -> gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
    gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (inst env b P)).
Proof.
    intros n P A s s' HQ Hn HA Hb Hs H. destruct (qfrag_cases env P HQ) as [HP|[cs [EP [HSi [Hcs _]]]]];
        [exact (generic_parameter b K Hnv n P A s s' HP Hn HA Hb Hs H)|].
    assert (Hcn: forall C, In C cs -> args_narrowed env C = true).
    { intros C HC. assert (E: forallb (nullable_narrowed env) cs = true) by (destruct EP as [-> | ->]; exact Hn).
      rewrite forallb_forall in E.
      destruct C as [m c args|[m c args|n'|g|me msg|v o n'|g|cs']|g|me msg|v o n'|g|cs']; try reflexivity; exact (E _ HC). }
    assert (HbI: bound_in env b K [] (Intersection (map to_generic cs)) = true) by (destruct EP as [-> | ->]; exact Hb).
    (* below the instance of each component, below that of the intersection *)
    assert (Hinter: forall k A0, yfrag b A0 -> unify env k (Intersection cs) A0 (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> below A0 (inst_nested env b (Intersection (map to_generic cs)))
            /\ (of_fragment (inst_nested env b (Intersection (map to_generic cs)))
                \/ exists xs, inst_nested env b (Intersection (map to_generic cs)) = Intersection xs))).
    { intros k A0 HA0 E. destruct (gparam_components k cs A0 s s' HSi Hcs Hcn HA0 HbI Hs E) as [Hs' [Hn' [HnA Hall]]].
      split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb.
      pose proof (gsatisfies_of_fragment b s' Hsb) as Hbf.
      destruct (components_sfrag_facts env _ Hcs) as [Hl Hcsf].
      change (inst_nested env b (Intersection (map to_generic cs)))
          with (of_components env (flat_map intersected_components (map (inst_component env b) (map to_generic cs)))).
      rewrite (map_ext_in (inst_component env b) (inst_nested env b) (map to_generic cs))
          by (intros c Hc; exact (inst_component_nested env b c (proj1 (Hcsf c Hc)))).
      refine ((fun Hb => conj (proj1 Hb) (proj2 (proj2 (proj2 Hb))))
          (below_of_components A0 _ (proj1 HA0) HnA ltac:(rewrite length_map; exact Hl) _)).
      intros y Hy. apply in_map_iff in Hy. destruct Hy as [c [<- Hc]]. apply in_map_iff in Hc. destruct Hc as [C [<- HC]].
      split; [|exact (Hall Hsb C HC)].
      destruct (param_component_cases env wf cs C HSi Hcs HC) as [[m [cl [args EC]]]|[gm [nn [q EC]]]].
      - exact (instance_of_fragment b K Hnv C Hbf (compfrag_ifrag env C (HSi C HC) ltac:(rewrite EC; reflexivity)) (Hcn C HC)
          (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC))).
      - pose proof (bound_in_component env b K [] _ _ HbI (in_map _ _ _ HC)) as HbC. rewrite EC in HbC |- *.
        destruct (binds_ref_some env wf b K [] (mkGenericRef gm nn q []) HbC) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        change (inst_nested env b (to_generic (TypeVariable (mkGenericRef gm nn q [])))) with (inst env b (TypeVariable (mkGenericRef gm nn q []))).
        rewrite (proj1 (inst_reference env b gm nn q [] _ _ _ Ex)). exact (ref_apply_of_fragment gm nn x (Hbf q o x Ex)). }
    destruct EP as [->| ->].
    - destruct (Hinter n A HA H) as [Hs' [Hn' Hsnd]]. split; [exact Hs'|]. split; [exact Hn'|].
      intros Hsb. exact (proj1 (Hsnd Hsb)).
    - (* nullable: the intersection takes the argument without null *)
      destruct n as [|n]; [discriminate H|]. rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
      destruct (Hinter n _ (yfrag_nullable_assignee b A HA) H) as [Hs' [Hn' Hsnd]].
      split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb. destruct (Hsnd Hsb) as [Hbx Hfx].
      change (inst env b (Nullable (Intersection cs))) with (rewrap_nullable (inst_nested env b (Intersection (map to_generic cs)))).
      destruct Hfx as [Hfx|[xs Ex]]; [exact (nullable_variable_below false A _ (proj1 (proj1 HA)) (proj1 Hfx) Hbx)|].
      rewrite Ex in Hbx |- *. destruct Hbx as [f Hf]. exists (S f). cbn [rewrap_nullable].
      rewrite (nullable_target f _ A [] (proj1 (proj1 HA))). exact Hf.
Qed.

End ParameterIntersections.

(* ---------------------------------------------------------------------------------------------- *)
(* Invocations                                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * Inference is sound with the type parameters of the caller in the arguments: where unify accepts each
 * argument of an invocation for its parameter, in turn, each argument fits its parameter with the type
 * variables replaced by any types that satisfy the variable states it ends with. As
 * Constraints.invocation_sound.
 *)
Theorem generic_invocation_sound: forall n Ps As s0 u b K,
    (* the type parameters of non-null bounds bound to types that aren't nullable *)
    nonnull_values b ->
    gwf_states s0 ->
    (forall P, In P Ps -> qfrag env P = true /\ bound_in env b K [] (pgeneric P) = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (forall A, In A As -> yfrag b A) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    gwf_states u /\ (gsatisfies b u -> forall P A, In (P, A) (combine Ps As) -> below A (inst env b P)).
Proof.
    intros n Ps As s0 u b K Hnv Hs0 HPs HPn HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (inst env b P))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP HbP]. exact (generic_qparameter b K Hnv n P A s s' HfP (HPn P HP) (HAs A HA) HbP Hs E). }
    destruct (gfold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros Hb P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    exact (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hb)).
Qed.

(* The final value of a variable that isn't bound exactly is within its bounds *)
Lemma generic_final_value_fits: forall s p st o, gwf_states s -> lookup_state s p = Some st -> is_exact st = false ->
    of_fragment (Constraints.final_value env st) -> gfits st o (Constraints.final_value env st).
Proof.
    intros s p st o Hs Hl He Hf. destruct (proj1 Hs p st Hl) as [_ [_ [Hb _]]]. destruct (Hb He) as [_ [[K HK] _]].
    unfold gfits. rewrite He. pose proof (below_refl _ Hf) as Hr.
    unfold Constraints.final_value in Hf, Hr |- *. destruct (is_non_nullable_nothing env (lower_bound st)).
    - split; [exists K; exact HK|exact Hr].
    - split; [exact Hr|exists K; exact HK].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Member calls                                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma of_fragment_of_class: forall t, in_fragment env t = true -> of_fragment t.
Proof. exact (in_fragment_of_fragment env declared). Qed.

(* The types of Fragment.v are types for inference, given the conjectures *)
Lemma generic_inference_types: inference_types env of_fragment of_fragment.
Proof.
    split.
    - intros x H. exact (proj1 H).
    - exact of_fragment_of_class.
    - exact below_refl.
    - exact of_fragment_of_class.
    - intros a c Ha Hc. exact (intersect_of_fragment a c Ha (of_fragment_of_class c Hc)).
    - intros a c Ha Hc. exact (supertype_of_fragment a c Ha (of_fragment_of_class c Hc)).
    - intros a c x n Ha Hc Hx H. pose proof (of_fragment_of_class c Hc) as Hc'.
      pose proof (intersect_of_fragment a c Ha Hc') as Hi. destruct (intersect_below_both a c Ha Hc') as [H1 H2].
      split; [exact (below_trans x _ a Hx Hi Ha (ex_intro _ n H) H1)|exact (below_trans x _ c Hx Hi Hc' (ex_intro _ n H) H2)].
    - intros a c x n Ha Hc Hx H. pose proof (of_fragment_of_class c Hc) as Hc'.
      pose proof (supertype_of_fragment a c Ha Hc') as Hs. destruct (below_supertype a c Ha Hc') as [H1 H2].
      split; [exact (below_trans a _ x Ha Hs Hx H1 (ex_intro _ n H))|exact (below_trans c _ x Hc' Hs Hx H2 (ex_intro _ n H))].
    - exact intersect_no_vars.
    - exact supertype_no_vars.
    - intros gm nn x a n Hx Ha Hgm Hnn H.
      exact (gaccepts a _ (of_fragment_of_class a Ha) (ref_apply_of_fragment gm nn x Hx)
          (instance_never_fails env wf declared declared_wf n gm nn x a (proj1 Hx) (in_fragment_is_gfrag env a Ha) Hgm Hnn H)).
    - intros gm nn x a n Hx Ha H.
      exact (gaccepts _ a (ref_apply_of_fragment gm nn x Hx) (of_fragment_of_class a Ha)
          (instance_assigned_never_fails env wf declared declared_wf n gm nn x a (proj1 Hx) (in_fragment_is_gfrag env a Ha) H)).
    - intros gm nn x B n Hx HB H.
      exact (gaccepts _ _ (ref_apply_of_fragment gm nn x Hx) (of_fragment_of_class _ (bound_apply_in_fragment env gm nn B HB))
          (instance_within_never_fails env wf declared declared_wf n gm nn x B (proj1 Hx) HB H)).
Qed.

(* The type parameters of the caller in the ownership of type arguments: none of ids *)
Definition ownership_outside (ids: list TypeParameterId) (o: Ownership): Prop :=
    match o with parameter_ownership q => ~ In q ids | _ => True end.

Fixpoint owners_outside_h (ids: list TypeParameterId) (bound_owners_outside: TypeParameterId -> Prop) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => owners_outside_h ids bound_owners_outside a /\ acc) True arguments
    | Nullable n => owners_outside_h ids bound_owners_outside n
    | Generic g => bound_owners_outside (param_of g)
    | TypeArgument _ o n => ownership_outside ids o /\ owners_outside_h ids bound_owners_outside n
    | Intersection cs => fold_right (fun c acc => owners_outside_h ids bound_owners_outside c /\ acc) True cs
    | _ => True
    end.

(* Of a reference, in the declared bound of its parameter (see Subtyping.through_param) *)
Definition param_owners_outside (ids: list TypeParameterId) (p: TypeParameterId): Prop := through_param env (owners_outside_h ids) True p.

Fixpoint owners_outside (ids: list TypeParameterId) (t: EType): Prop :=
    match t with
    | RootResolved _ _ arguments => fold_right (fun a acc => owners_outside ids a /\ acc) True arguments
    | Nullable n => owners_outside ids n
    | Generic g => param_owners_outside ids (param_of g)
    | TypeArgument _ o n => ownership_outside ids o /\ owners_outside ids n
    | Intersection cs => fold_right (fun c acc => owners_outside ids c /\ acc) True cs
    | _ => True
    end.

Lemma owners_outside_top: forall ids t, owners_outside ids t = owners_outside_h ids (param_owners_outside ids) t.
Proof.
    intros ids. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs]; simpl; try reflexivity; try exact (IH n).
    - induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

Lemma owners_outside_h_agree: forall ids p k U1 U2, (forall q, q = p \/ parameter_rank env q < k -> U1 q = U2 q) ->
    forall t, deep_ranked env p k t = true -> owners_outside_h ids U1 t = owners_outside_h ids U2 t.
Proof.
    intros ids p k U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try reflexivity; try exact (IH n Ht).
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - exact (HU _ (deep_ranked_param env p k g Ht)).
    - rewrite (IH n Ht). reflexivity.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma owners_outside_h_mono: forall ids U1 U2, (forall q, U1 q -> U2 q) -> forall t, owners_outside_h ids U1 t -> owners_outside_h ids U2 t.
Proof.
    intros ids U1 U2 HU. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Ht; simpl in Ht |- *; try exact Ht; try exact (IH n Ht).
    - induction args as [|a args IHa]; [exact I|]. destruct Ht as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (HU _ Ht).
    - destruct Ht as [Ho Hn]. exact (conj Ho (IH n Hn)).
    - induction cs as [|c cs IHc]; [exact I|]. destruct Ht as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

Lemma param_owners_outside_iff: forall ids p, param_owners_outside ids p <-> owners_outside ids (parameter_bound env p).
Proof.
    intros ids p. rewrite owners_outside_top. unfold param_owners_outside at 1.
    exact (through_param_fix_prop env (owners_outside_h ids) deep (owners_outside_h_agree ids)
        (fun U1 U2 t H => owners_outside_h_mono ids U1 U2 H t) p).
Qed.

Lemma fold_and_intro: forall (Q: EType -> Prop) l, (forall a, In a l -> Q a) -> fold_right (fun a acc => Q a /\ acc) True l.
Proof.
    intros Q l H. induction l as [|a l IH]; [exact I|]. split; [apply H; left; reflexivity|].
    apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma owners_outside_free: forall ids b, (forall q, ~ In q ids -> lookup_binding b q = None) ->
    forall t, owners_outside ids t -> owners_free b t.
Proof.
    intros ids b Hb.
    (* the declared bounds of the type parameters, by their ranks *)
    assert (Hparam: forall p, param_owners_outside ids p -> param_owners_free b p).
    { intros p. remember (parameter_rank env p) as r eqn:Er. revert p Er. induction r as [r IH] using lt_wf_ind. intros p -> H.
      unfold param_owners_free. rewrite (through_param_eq env (owners_free_h b) True deep (owners_free_h_agree b) p).
      apply param_owners_outside_iff in H. pose proof (deep p) as Hd. revert H Hd. generalize (parameter_bound env p) as t.
      fix IHt 1. intros [m c args|n|g|me msg|v o n|g|cs] H Hd; simpl in H, Hd |- *; try exact I.
      - induction args as [|a args IHa]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd. destruct H as [Ha Has].
        exact (conj (IHt a Ha (proj1 Hd)) (IHa Has (proj2 Hd))).
      - exact (IHt n H Hd).
      - destruct (deep_ranked_param env p _ g Hd) as [Hp|Hr]; [rewrite Hp; unfold param_eqb; rewrite Nat.eqb_refl; exact I|].
        destruct (param_eqb (param_of g) p); [exact I|]. exact (IH _ Hr _ eq_refl H).
      - destruct H as [Ho Hn]. split; [destruct o as [| | |q]; try exact I; exact (Hb q Ho)|exact (IHt n Hn Hd)].
      - induction cs as [|c cs IHc]; [exact I|]. simpl in Hd. apply andb_true_iff in Hd. destruct H as [Hc Hcs].
        exact (conj (IHt c Hc (proj1 Hd)) (IHc Hcs (proj2 Hd))). }
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try exact I.
    - induction args as [|a args IHa]; [exact I|]. destruct H as [Ha Has]. exact (conj (IH a Ha) (IHa Has)).
    - exact (IH n H).
    - exact (Hparam _ H).
    - destruct H as [Ho Hn]. split; [destruct o as [| | |q]; try exact I; exact (Hb q Ho)|exact (IH n Hn)].
    - induction cs as [|c cs IHc]; [exact I|]. destruct H as [Hc Hcs]. exact (conj (IH c Hc) (IHc Hcs)).
Qed.

Lemma lookup_map_none: forall (l: list (TypeParameterId * EType)) (g: TypeParameterId * EType -> EType) p,
    ~ In p (map fst l) -> lookup_binding (map (fun v => (fst v, g v)) l) p = None.
Proof.
    intros l g p. induction l as [|[q bq] l IH]; intros H; [reflexivity|]. simpl.
    destruct (param_eqb p q) eqn:E; [apply param_eqb_eq in E; subst q; exfalso; apply H; left; reflexivity|].
    apply IH. intros Hin. apply H. right. exact Hin.
Qed.

(* A class type mentions Nothing only as `exclusive Nothing`, where it does only as the bottom type *)
Lemma class_bottom_only: forall t, in_fragment env t = true -> nothing_is_bottom t = true -> bottom_only t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hf Hn; try (cbn [in_fragment] in Hf; discriminate Hf).
    - destruct (root_in_fragment env m c args Hf) as [_ Hargs]. cbn [nothing_is_bottom] in Hn. cbn [bottom_only].
      apply andb_true_iff in Hn. destruct Hn as [Hc Hns]. rewrite Hc. cbn [andb]. clear Hf Hc.
      induction args as [|a args IHa]; [reflexivity|]. cbn [forallb] in Hns |- *. apply andb_true_iff in Hns. destruct Hns as [Ha Has].
      rewrite (IHa Has (fun x Hx => Hargs x (or_intror Hx))), andb_true_r.
      pose proof (Hargs a (or_introl eq_refl)) as Hfa.
      destruct a as [| | | |v o n| |]; cbn [argument_in_fragment] in Hfa; try discriminate Hfa.
      cbn [nothing_is_bottom] in Ha. cbn [bottom_only]. exact (IH n Hfa Ha).
    - destruct (fragment_cases env _ Hf) as [[? [? [? E]]]|[m [c [args [E Hr]]]]]; [discriminate E|]. injection E as En.
      rewrite <- En in Hr. exact (IH n Hr Hn).
Qed.

(* ... and a class type without ownerships of type parameters has none of any *)
Lemma closed_owners_outside: forall ids t, in_fragment env t = true -> closed t = true -> owners_outside ids t.
Proof.
    intros ids. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] Hf Hc; try (cbn [in_fragment] in Hf; discriminate Hf).
    - destruct (root_in_fragment env m c args Hf) as [_ Hargs]. change (forallb closed args = true) in Hc. cbn [owners_outside].
      clear Hf. induction args as [|a args IHa]; [exact I|]. cbn [forallb] in Hc. apply andb_true_iff in Hc. destruct Hc as [Ha Has].
      split; [|exact (IHa Has (fun x Hx => Hargs x (or_intror Hx)))].
      pose proof (Hargs a (or_introl eq_refl)) as Hfa.
      destruct a as [| | | |v o n| |]; cbn [argument_in_fragment] in Hfa; try discriminate Hfa.
      destruct (closed_argument v o n Ha) as [Hop Hcn]. cbn [owners_outside].
      split; [destruct o; first [exact I|discriminate Hop]|exact (IH n Hfa Hcn)].
    - destruct (fragment_cases env _ Hf) as [[? [? [? E]]]|[m [c [args [E Hr]]]]]; [discriminate E|]. injection E as En.
      rewrite <- En in Hr. exact (IH n Hr Hc).
Qed.

(*
 * Calling a member function in generic code is sound: as FinalValues.member_call_with_any_final_values_sound,
 * with the types of the arguments of the fragment of Fragment.v, mentioning the type parameters of the
 * caller, rather than class types. Their bounds must not be Nothing, nor must an intersection among
 * them be one of unrelated classes (bottom_only): unify takes those for Nothing, which they have no
 * values of either; and the type parameters of the caller are none of those inferred.
 *)
Theorem member_call_in_generic_code_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the bounds: the declared ones *)
    (forall p bound, In (p, bound) (cvars ++ ovars) -> to_generic bound = parameter_bound env p) ->
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
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> qfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (forall A, In A As -> of_fragment A /\ bottom_only A = true /\ owners_outside (map fst (cvars ++ ovars)) A /\ Qb A) ->
    (forall p bound, In (p, bound) ovars -> Qb bound) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values are of Qb *)
    (forall p bound, In (p, bound) ovars -> Qb (final_value_of env U p))
    /\ forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    (* the types of the parameters are bound in b, which binds the type parameters of c to the type
       arguments of the object, and those of the function to their final values *)
    (exists K, forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true)
    /\ (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> is_exact_ownership o = true
        /\ (In (TypeArgument Model.invariant o x) zs \/ exists bound, In (p, bound) ovars /\ x = final_value_of env U p))
    (* the values, within their bounds *)
    /\ plain_values b
    /\ (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) ->
        exists bound, In (p, bound) (cvars ++ ovars) /\ of_fragment x /\ below x bound)
    /\ forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hdecl Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HPn HAs HQbounds Hfold.
    pose proof (object_arguments_exact env wf c mo e xs zs He (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) Hfo Hxx Hzs)
        as Hzx.
    destruct (receiver_and_object env wf of_fragment of_fragment generic_inference_types
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu0 [Hp Hrest]]]]]]]]].
    assert (Hwfu: gwf_states u).
    { split; [exact Hwfu0|]. intros p st Hl' He'. destruct (Hrest p st Hl' He') as [bound [Hin ->]].
      cbn [upper_bound lower_bound static_upper_bound]. rewrite (initial_in_fragment env bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin)))).
      split; [exact (HQbounds p bound Hin)|]. split; [exact Qb_bottom|].
      exact (in_fragment_no_vars env bound (Hbounds p bound (in_or_app _ _ _ (or_intror Hin)))). }
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    (* the arguments, as the types of the arguments of the bindings over vars *)
    assert (HAs': forall b', (forall q, ~ In q (map fst vars) -> lookup_binding b' q = None) -> forall A, In A As -> yfrag b' A).
    { intros b' Hb' A HA. destruct (HAs A HA) as [Hf [Hbo [Ho Hq]]]. split; [exact Hf|]. split; [exact Hbo|].
      split; [exact (owners_outside_free _ b' Hb' A Ho)|exact Hq]. }
    (* the variable states unify ends with, with the bounds themselves for the type parameters *)
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (refs_fuel env wf of_fragment of_fragment generic_inference_types vars b0 Hbounds) as [K0 [HK0 HK0r]].
    { intros p bound Hin. exists ref, bound. split; [unfold b0; exact (lookup_map_vars vars _ p bound Hnd' Hin)|].
      split; [reflexivity|]. split; [exact (of_fragment_of_class _ (Hbounds p bound Hin))|]. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (pgeneric P) = true).
    { intros P HP. apply (pbound_in_from_refs env wf vars _ _ P (proj1 (HPs P HP)) (proj2 (HPs P HP)) HK0 HK0r).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    (* the bounds themselves, of the nullability of the declared ones *)
    assert (Hb0nn: nonnull_values b0).
    { intros q o x E Hq. unfold b0 in E.
      destruct (lookup_map_pairs vars (fun v => TypeArgument Model.invariant ref (snd v)) q _ E) as [[q' bound] [Hin [Hf Ea]]].
      cbn [fst snd] in Hf, Ea. subst q'. injection Ea as _ ->.
      rewrite (is_nullable_generic env ranked), (effective_bound_plain env ranked), <- (Hdecl q bound Hin), is_nullable_to_generic in Hq.
      exact Hq. }
    destruct (generic_invocation_sound nf Ps As u U b0 K0 Hb0nn Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb0 P HP)) HPn
        (HAs' b0 (fun q Hq => lookup_map_none vars _ q Hq)) Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep [Hkeep2 _]].
    assert (Hfinal': forall p bound, In (p, bound) ovars -> of_fragment (final_value_of env U p)).
    { intros p bound Hin.
      destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (proj1 HwfU p st2 HlU) as [_ [_ [Hw _]]]. destruct (Hw He2) as [_ [_ [Hbu [Hbl _]]]].
      unfold final_value_of, Constraints.final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    split.
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (proj2 HwfU p st2 HlU He2) as [Hqu [Hql _]].
      unfold final_value_of, Constraints.final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    intros b Hbdef.
    (* the type parameters of the function: their final values, below their bounds *)
    assert (Hfin: forall p bound, In (p, bound) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ final_value_of env U p = Constraints.final_value env st /\ gfits st ref (Constraints.final_value env st)
        /\ exists f, unify env f bound (Constraints.final_value env st) (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 [_ Hst2]]]].
      pose proof (Hfinal' p bound Hin) as Hff. unfold final_value_of in Hff. rewrite HlU in Hff.
      pose proof (generic_final_value_fits U p st2 ref HwfU HlU He2 Hff) as Hfit.
      exists st2. split; [exact HlU|]. split; [exact He2|]. split; [unfold final_value_of; rewrite HlU; reflexivity|].
      split; [exact Hfit|].
      destruct (proj1 HwfU p st2 HlU) as [_ [_ [Hw _]]]. destruct (Hw He2) as [_ [_ [_ [_ Hbs]]]].
      destruct (proj2 HwfU p st2 HlU He2) as [_ [_ Hsc]]. unfold static_ok in Hbs. rewrite Hsc in Hbs.
      unfold gfits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
      destruct (Hbs _ K2 Hff E2) as [f Ef]. cbn [static_upper_bound] in Hst2. rewrite Hst2 in Ef. exists f. exact Ef. }
    (* the type arguments of b, within the bounds *)
    assert (Hlookup: forall p bound, In (p, bound) vars -> exists o x, lookup_binding b p = Some (TypeArgument Model.invariant o x)
        /\ is_exact_ownership o = true /\ of_fragment x
        /\ exists f, unify env f bound x (Ongoing []) = Some (Ongoing [])).
    { intros p bound Hin. rewrite Hbdef, lookup_app. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct (In_nth_error _ _ Hin) as [i Hi].
        assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
        destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (lookup_parameter env wf c zs i p z Hpi Hz).
        destruct (Hzb i p bound z Hi Hz) as [o [x [f [-> Ef]]]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        exists o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact (of_fragment_of_class _ Hx)|]. exists f. exact Ef.
      - assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
        assert (Hndo: NoDup (map fst ovars)).
        { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
          inversion H. apply IH. assumption. }
        rewrite (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (final_value_of env U (fst v))) p bound Hndo Hin).
        cbn [fst]. exists ref, (final_value_of env U p). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (Hfinal' p bound Hin)|].
        destruct (Hfin p bound Hin) as [st [_ [_ [-> [_ Ef]]]]]. exact Ef. }
    destruct (refs_fuel env wf of_fragment of_fragment generic_inference_types vars b Hbounds Hlookup) as [K [HK HKr]].
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (pgeneric P) = true).
    { intros P HP. apply (pbound_in_from_refs env wf vars _ _ P (proj1 (HPs P HP)) (proj2 (HPs P HP)) HK HKr).
      intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    (* the type parameters of the caller are none of those inferred *)
    assert (Hbnone: forall q, ~ In q (map fst vars) -> lookup_binding b q = None).
    { intros q Hq. rewrite Hbdef, lookup_app.
      assert (Hnc: ~ In q (parameter_ids env c)).
      { rewrite <- Hids. intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. left. exact Hin. }
      rewrite (lookup_combine_none _ zs q Hnc: lookup_binding (bindings_of env c zs) q = None).
      apply (lookup_map_none ovars (fun v => TypeArgument Model.invariant ref (final_value_of env U (fst v))) q).
      intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. right. exact Hin. }
    (* the values of non-null bounds, within them, aren't null *)
    assert (Hnv: nonnull_values b).
    { intros p o x Hpb Hpn. pose proof Hpb as Hpb'.
      assert (Hin: exists bound, In (p, bound) vars).
      { rewrite Hbdef, lookup_app in Hpb'. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
        - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
          rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
          simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
        - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) p _ Hpb') as [_ Hin].
          apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
          exists bound. apply in_or_app. right. exact Hin. }
      destruct Hin as [bound Hin]. destruct (Hlookup p bound Hin) as [o' [x' [Hl' [_ [Hfx Hbx]]]]].
      rewrite Hpb in Hl'. injection Hl' as <- <-.
      exact (within_bound_not_nullable p bound x (Hdecl p bound Hin) (in_fragment_is_gfrag env _ (Hbounds p bound Hin)) (proj1 Hfx) Hbx Hpn). }
    destruct (generic_invocation_sound nf Ps As u U b K Hnv Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb P HP)) HPn
        (HAs' b Hbnone) Hfold) as [_ Hsound].
    (* the type arguments satisfy the variable states unify ends with *)
    assert (Hsat: gsatisfies b U).
    { intros p o x Hpb.
      assert (Hin: exists bound, In (p, bound) vars).
      { rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
        - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
          rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
          simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
        - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) p _ Hpb) as [_ Hin].
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
        split; [exact (of_fragment_of_class _ Hfx)|]. exists (mkVariableState bound y y true true).
        split; [exact (Hkeep p _ (Hcap i p bound y Hi Hy) eq_refl)|].
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy2.
        destruct y as [| | | |vb ob X| |]; try discriminate Hfy2.
        unfold gfits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n1. split; [reflexivity|]. split; [reflexivity|].
        split; [exact (of_fragment_of_class _ Hfy2)|]. split; [exact (of_fragment_of_class _ Hfx)|].
        apply (unify_fuel_monotone env n1); [lia|]. exact (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy).
      - (* a type parameter of the function: its final value *)
        assert (Hnin: ~ In p (parameter_ids env c))
            by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
        rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None) in Hpb.
        destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) p _ Hpb) as [Ea _].
        injection Ea as Eo2 Ex2. subst o x.
        destruct (Hfin p bound Hin) as [st [HlU [_ [Hfv [Hfit _]]]]].
        split; [exact (Hfinal' p bound Hin)|]. exists st. split; [exact HlU|]. rewrite Hfv. exact Hfit. }
    split; [exists K; exact Hb|]. split.
    { intros p o x Hpb. rewrite Hbdef, lookup_app in Hpb.
      destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
      - injection Hpb as ->. destruct (lookup_combine_nth _ zs p _ Ec) as [i [_ Hz]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex. simpl in Hex. apply andb_true_iff in Hex.
        split; [exact (proj1 Hex)|left; exact (nth_error_In _ _ Hz)].
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) p _ Hpb) as [Ea Hin].
        injection Ea as Eo Ex. subst o x. split; [reflexivity|right].
        apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1. exists bound. split; [exact Hin|reflexivity]. }
    split.
    { intros q a Eq. rewrite Hbdef, lookup_app in Eq. destruct (lookup_binding (bindings_of env c zs) q) as [a'|] eqn:Ec.
      - injection Eq as <-. destruct (lookup_combine_nth _ zs q _ Ec) as [i [_ Hz]].
        pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex.
        destruct a' as [| | | |[] o x| |]; try discriminate Hex. simpl in Hex. apply andb_true_iff in Hex. destruct Hex as [Ho Hx].
        split; [destruct o; first [reflexivity|discriminate Ho]|].
        exists o, x. split; [reflexivity|exact (gfrag_not_nested env _ (in_fragment_is_gfrag env _ Hx))].
      - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) q _ Eq) as [Ea Hin].
        subst a. apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
        split; [reflexivity|]. exists ref, (final_value_of env U q). split; [reflexivity|].
        exact (gfrag_not_nested env _ (proj1 (Hfinal' q bound Hin))). }
    split.
    { intros p o x Hpb. pose proof Hpb as Hpb'.
      assert (Hin: exists bound, In (p, bound) vars).
      { rewrite Hbdef, lookup_app in Hpb'. destruct (lookup_binding (bindings_of env c zs) p) as [a|] eqn:Ec.
        - destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi _]]. change (nth_error (parameter_ids env c) i = Some p) in Hi.
          rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 bound]|] eqn:Ev; [|discriminate Hi].
          simpl in Hi. injection Hi as ->. exists bound. apply in_or_app. left. exact (nth_error_In _ _ Ev).
        - destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (final_value_of env U q)) p _ Hpb') as [_ Hin].
          apply in_map_iff in Hin. destruct Hin as [[p1 bound] [Hfst Hin]]. simpl in Hfst. subst p1.
          exists bound. apply in_or_app. right. exact Hin. }
      destruct Hin as [bound Hin]. destruct (Hlookup p bound Hin) as [o' [x' [Hl' [_ [Hfx Hbx]]]]].
      rewrite Hpb in Hl'. injection Hl' as <- <-. exists bound. split; [exact Hin|]. split; [exact Hfx|exact Hbx]. }
    intros P A HPA. destruct (Hsound Hsat P A HPA) as [f Ef].
    exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* Member calls with static upper bounds with type variables, in generic code                     *)
(* ---------------------------------------------------------------------------------------------- *)

(*
 * A call in generic code of a member function whose type parameters are bounded by types mentioning
 * them, and the type parameters of the class it is declared in: as
 * generic_invocation_with_bounded_variables_sound, with the receiver as member_call_in_generic_code_sound
 * has it. The type parameters of the class are bound to the type arguments of the object as that
 * class, those of the function to their final values, of Qb.
 *)
Theorem generic_member_call_with_bounded_variables_sound: forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p S, In (p, S) cvars -> in_fragment env S = true) ->
    (* the bounds of the type parameters of c: the declared ones *)
    (forall p S, In (p, S) cvars -> to_generic S = parameter_bound env p) ->
    (forall p S, In (p, S) ovars -> gstatic_bound (cvars ++ ovars) p S) ->
    (* the receiver, unified with the receiver parameter *)
    in_fragment env (RootResolved ma ca ys) = true ->
    unify env n (RootResolved mr c (map receiver_leaf cvars)) (RootResolved ma ca ys)
        (for_inference_of (cvars ++ ovars) (map fst cvars)) = Some (Ongoing u) ->
    (* the object it is; its type arguments are exact *)
    in_fragment env (RootResolved mo e xs) = true ->
    is_assignable_to env n0 (RootResolved mo e xs) (RootResolved ma ca ys) = Some true ->
    zs = (if class_eqb e c then xs else parameterized_supertype_arguments env e xs c) ->
    (forall x, In x xs -> exact_argument env x = true) ->
    (* ... within the bounds of the type parameters of c *)
    (forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z ->
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f S x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> qfrag env P = true /\ (forall C, In C (intersected_components P) -> plain_owners C = true)
        /\ vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) P = true) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (forall p S st, In (p, S) ovars -> no_vars S = false -> lookup_state U p = Some st ->
        is_non_nullable_nothing env (lower_bound st) = false) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (gfinal_of U (fst v)))) ovars ->
    (forall A, In A As -> yfrag b A) ->
    (forall t, Qb t -> owners_free b t) ->
    plain_values b
    /\ (forall q, In q (map fst (cvars ++ ovars)) -> bound_b b q = true)
    /\ (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> In (TypeArgument Model.invariant o x) zs \/ Qb x)
    /\ (forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x
        /\ ((exists i S, nth_error cvars i = Some (q, S) /\ nth_error zs i = Some (TypeArgument Model.invariant o x))
            \/ exists S, In (q, S) ovars /\ x = gfinal_of U q))
    /\ (forall p S, In (p, S) ovars -> Qb (gfinal_of U p)
        /\ forall C, In C (bound_components S) -> below (gfinal_of U p) (instantiate_free env b C))
    /\ (forall P A, In (P, A) (combine Ps As) -> below A (instantiate_free env b P)).
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hcb Hcdecl Hst Hfy Hrec Hfo Hobj Hzs Hxx
        Hzb HPs HPn Hfold Hlow b Hbdef HAs Hown.
    pose proof (object_arguments_exact env wf c mo e xs zs He (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) Hfo Hxx Hzs)
        as Hzx.
    destruct (receiver_captures env wf n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hcb Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hdomu [Hp _]]]]]]]]].
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    assert (Hndo: NoDup (map fst ovars)).
    { clear -Hnd. revert Hnd. generalize (map fst ovars). induction (map fst cvars) as [|x l IH]; intros l2 H; [exact H|].
      inversion H. apply IH. assumption. }
    (* the states after the receiver: the type parameters of c captured, those of the function as they start *)
    assert (Hwfu: gwf2 u).
    { intros p st Hp'. destruct (Hdomu p st Hp') as [Hin|[S Hin]].
      - apply in_map_iff in Hin. destruct Hin as [[p1 S] [Hfst Hin]]. simpl in Hfst. subst p1.
        destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        rewrite (Hcap i p S y Hi Hy) in Hp'. injection Hp' as <-. unfold gstate_ok.
        cbn [upper_bound lower_bound is_exact static_upper_bound].
        pose proof (argument_in_fragment_no_vars env y (Hys y (nth_error_In _ _ Hy))) as Hny.
        split; [exact Hny|]. split; [exact Hny|]. split; [intros E; discriminate E|].
        exact (no_vars_in _ _ (in_fragment_no_vars env S (Hcb p S Hin))).
      - rewrite (Hownu p S Hin) in Hp'. injection Hp' as <-. exact (ginitial_ok _ p S u (Hst p S Hin)). }
    (* the bindings: the type arguments of the object as c, and the final values of the function's *)
    assert (HlbC: forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z -> lookup_binding b p = Some z).
    { intros i p S z Hi Hz. assert (Hpi: nth_error (parameter_ids env c) i = Some p) by (rewrite <- Hids, nth_error_map, Hi; reflexivity).
      rewrite Hbdef, lookup_app, (lookup_parameter env wf c zs i p z Hpi Hz). reflexivity. }
    assert (HlbO: forall p S, In (p, S) ovars -> lookup_binding b p = Some (TypeArgument Model.invariant ref (gfinal_of U p))).
    { intros p S Hin.
      assert (Hnin: ~ In p (parameter_ids env c))
          by (rewrite <- Hids; intros Hc2; exact (nodup_app_disjoint _ _ p Hnd Hc2 (in_map fst _ _ Hin))).
      rewrite Hbdef, lookup_app, (lookup_combine_none _ zs p Hnin: lookup_binding (bindings_of env c zs) p = None).
      exact (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (gfinal_of U (fst v))) p S Hndo Hin). }
    assert (Hlb_in: forall q a, lookup_binding b q = Some a ->
        (exists i S z, nth_error cvars i = Some (q, S) /\ nth_error zs i = Some z /\ a = z)
        \/ exists S, In (q, S) ovars /\ a = TypeArgument Model.invariant ref (gfinal_of U q)).
    { intros p a Hpb. rewrite Hbdef, lookup_app in Hpb. destruct (lookup_binding (bindings_of env c zs) p) as [a'|] eqn:Ec.
      - injection Hpb as <-. left. destruct (lookup_combine_nth _ zs p _ Ec) as [i [Hi Hz]].
        change (nth_error (parameter_ids env c) i = Some p) in Hi.
        rewrite <- Hids, nth_error_map in Hi. destruct (nth_error cvars i) as [[p1 S]|] eqn:Ev; [|discriminate Hi].
        simpl in Hi. injection Hi as ->. exists i, S, a'. split; [exact Ev|]. split; [exact Hz|reflexivity].
      - right. destruct (lookup_own ovars (fun q => TypeArgument Model.invariant ref (gfinal_of U q)) p _ Hpb) as [Ea Hin].
        apply in_map_iff in Hin. destruct Hin as [[p1 S] [Hfst Hin]]. simpl in Hfst. subst p1. exists S. split; [exact Hin|exact Ea]. }
    assert (Hzarg: forall i p S z, nth_error cvars i = Some (p, S) -> nth_error zs i = Some z ->
        exists o x, z = TypeArgument Model.invariant o x /\ is_exact_ownership o = true /\ in_fragment env x = true).
    { intros i p S z Hi Hz. pose proof (Hzx _ (nth_error_In _ _ Hz)) as Hex.
      destruct z as [| | | |[] o x| |]; try discriminate Hex. simpl in Hex. apply andb_true_iff in Hex.
      exists o, x. split; [reflexivity|exact Hex]. }
    (* the states the fold ends with: with no bindings at all *)
    assert (Hstep0: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf2 s -> unify env nf P A (Ongoing s) = Some (Ongoing s') ->
        gwf2 s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP [HoP _]]. destruct (HAs A HA) as [HfA [HbA [_ HqA]]].
      destruct (mqparameter [] plain_nil bf_nil gwf2 gwf2_capturable nf (fun k _ => gleaf_all k [])
          P A s s' HfP HoP (HPn P HP) nonnull_nil (conj HfA (conj HbA (conj (owners_free_nil A) HqA))) Hs E) as [Hs' [Hn' _]].
      split; [exact Hs'|exact Hn']. }
    destruct (mfold_chain gwf2 nf _ u U Hstep0 Hwfu Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep [Hkeep2 _]].
    (* the final values *)
    assert (Hfin: forall p S, In (p, S) ovars -> exists st, lookup_state U p = Some st /\ is_exact st = false
        /\ static_upper_bound st = S /\ gfinal_of U p = Constraints.final_value env st
        /\ of_fragment (gfinal_of U p) /\ gfits st ref (gfinal_of U p)).
    { intros p S Hin. destruct (Hkeep2 p _ (Hownu p S Hin) eq_refl eq_refl) as [st [Hl' [He' [_ Hs]]]].
      destruct (gfinal_value_fits U p st ref HwfU Hl' He') as [Hf Hfit].
      assert (Ef: gfinal_of U p = Constraints.final_value env st) by (unfold gfinal_of; rewrite Hl'; reflexivity).
      exists st. split; [exact Hl'|]. split; [exact He'|]. split; [exact Hs|]. split; [exact Ef|]. rewrite Ef. split; [exact Hf|exact Hfit]. }
    assert (Hpb: plain_values b).
    { intros q a Eq. destruct (Hlb_in q a Eq) as [[i [S [z [Hi [Hz ->]]]]]|[S [Hin ->]]].
      - destruct (Hzarg i q S z Hi Hz) as [o [x [-> [Ho Hx]]]]. split; [destruct o; first [reflexivity|discriminate Ho]|].
        exists o, x. split; [reflexivity|exact (gfrag_not_nested env _ (in_fragment_is_gfrag env _ Hx))].
      - split; [reflexivity|]. destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf _]]]]]].
        exists ref, (gfinal_of U q). split; [reflexivity|exact (gfrag_not_nested env _ (proj1 Hf))]. }
    assert (Hbf: forall q o x, lookup_binding b q = Some (TypeArgument Model.invariant o x) -> of_fragment x).
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - destruct (Hzarg i q S z Hi Hz) as [o' [x' [Ez' [_ Hx]]]]. rewrite Ez' in Ez. injection Ez as _ Ex. rewrite Ex.
        exact (of_fragment_of_class _ Hx).
      - injection Ea as _ Ex. rewrite Ex. destruct (Hfin q S Hin) as [_ [_ [_ [_ [_ [Hf _]]]]]]. exact Hf. }
    (* the type arguments satisfy the variable states unify ends with *)
    assert (Hsat: gsatisfies b U).
    { intros q o x Eq. split; [exact (Hbf q o x Eq)|]. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - (* of c: the type argument of the object, captured by that of the receiver *)
        destruct (nth_error_same_length cvars ys' i _ ltac:(lia) Hi) as [y Hy].
        exists (mkVariableState S y y true true). split; [exact (Hkeep q _ (Hcap i q S y Hi Hy) eq_refl)|].
        pose proof (Hys y (nth_error_In _ _ Hy)) as Hfy2.
        destruct y as [| | | |vb ob X| |]; try discriminate Hfy2.
        unfold gfits. cbn [is_exact upper_bound lower_bound]. exists vb, ob, X, n1. split; [reflexivity|]. split; [reflexivity|].
        split; [exact (of_fragment_of_class _ Hfy2)|]. split; [exact (Hbf q o x Eq)|].
        apply (unify_fuel_monotone env n1); [lia|]. rewrite Ez. exact (Forall2_nth_error _ zs ys' i _ _ Hp Hz Hy).
      - injection Ea as Eo Ex. subst o x. destruct (Hfin q S Hin) as [st [HlU [_ [_ [_ [_ Hfit]]]]]].
        exists st. split; [exact HlU|exact Hfit]. }
    assert (Hdomb: forall q, In q (map fst (cvars ++ ovars)) -> bound_b b q = true).
    { intros q Hq'. unfold bound_b. rewrite map_app in Hq'. apply in_app_or in Hq'.
      destruct Hq' as [Hq'|Hq']; apply in_map_iff in Hq'; destruct Hq' as [[q1 S] [Hfst Hin]]; simpl in Hfst; subst q1.
      - destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (nth_error_same_length cvars zs i _ ltac:(lia) Hi) as [z Hz].
        rewrite (HlbC i q S z Hi Hz). reflexivity.
      - rewrite (HlbO q S Hin). reflexivity. }
    assert (Hbound: forall t, vars_in (fun q => existsb (param_eqb q) (map fst (cvars ++ ovars))) t = true -> vars_in (bound_b b) t = true).
    { apply vars_in_mono. intros q E. apply existsb_exists in E. destruct E as [q' [Hq' Eq]]. apply param_eqb_eq in Eq. subst q'.
      exact (Hdomb q Hq'). }
    (* the final values, of Qb *)
    assert (Hqfin: forall p S, In (p, S) ovars -> Qb (gfinal_of U p)).
    { intros p S Hin. destruct (Hfin p S Hin) as [st [HlU [He' [_ [Ef _]]]]].
      destruct (HwfU p st HlU) as [_ [_ [Hw _]]]. destruct (Hw He') as [_ [_ [_ [_ [Hqu [Hql _]]]]]].
      rewrite Ef. unfold Constraints.final_value. destruct (is_non_nullable_nothing env (lower_bound st)); assumption. }
    split; [exact Hpb|]. split; [exact Hdomb|]. split.
    { intros q o x Eq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - left. rewrite Ez. exact (nth_error_In _ _ Hz).
      - right. injection Ea as _ ->. exact (Hqfin q S Hin). }
    split.
    { intros q o x Eq. split; [exact (Hbf q o x Eq)|]. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - left. exists i, S. split; [exact Hi|]. rewrite Ez. exact Hz.
      - right. exists S. split; [exact Hin|]. injection Ea as _ Ex. exact Ex. }
    (* the values of non-null bounds aren't null: the type arguments of the object and the final values,
       within the bounds *)
    assert (Hnv: nonnull_values b).
    { intros q o x Eq Hnq. destruct (Hlb_in q _ Eq) as [[i [S [z [Hi [Hz Ez]]]]]|[S [Hin Ea]]].
      - destruct (Hzb i q S z Hi Hz) as [o' [x' [f [Ez' Ef]]]]. rewrite Ez' in Ez. injection Ez as <- <-.
        exact (within_bound_not_nullable q S x (Hcdecl q S (nth_error_In _ _ Hi)) (in_fragment_is_gfrag env _ (Hcb q S (nth_error_In _ _ Hi)))
            (proj1 (Hbf q o x Eq)) (ex_intro _ f Ef) Hnq).
      - injection Ea as _ ->.
        destruct (Hfin q S Hin) as [st [HlU [He' [Hs [Ef _]]]]]. destruct (Hst q S Hin) as [ES [_ [Hcl _]]]. subst S.
        rewrite Ef. exact (gfinal_not_nullable U q st HwfU HlU He' ES (fun E => proj1 (Hcl E)) (fun E => Hlow q _ st Hin E HlU) Hnq). }
    (* the final values, within the static upper bounds *)
    assert (Hfinals: forall p S, In (p, S) ovars -> forall C, In C (bound_components S) ->
        below (gfinal_of U p) (instantiate_free env b C)).
    { intros p S Hin C HC. destruct (Hfin p S Hin) as [st [HlU [He' [Hs [Ef [Hf Hfit]]]]]].
      destruct (Hst p S Hin) as [_ [Hsv [Hcl _]]].
      destruct (HwfU p st HlU) as [_ [_ [Hw _]]]. destruct (Hw He') as [_ [_ [_ [Hfl [_ [Hql [_ Hok]]]]]]].
      unfold gstatic_ok in Hok. rewrite Hs in Hok. destruct (no_vars S) eqn:Ens.
      + (* without type variables: below the upper bound, which is below it, and its components *)
        destruct (Hcl eq_refl) as [HfS HqS]. unfold gfits in Hfit. rewrite He' in Hfit. destruct Hfit as [_ Hup].
        destruct (bound_component_of S C HfS HqS HC) as [HfC [HqC HSC]].
        rewrite (free_unmentioned env b Hpb C (proj1 HfC) (unmentioned b C (proj1 HfC) (Hown C HqC))).
        exact (below_trans _ S C Hf HfS HfC (Hok _ Hf Hup) HSC).
      + (* with them: the lower bound, checked against it *)
        destruct Hok as [[Hcomp _] Hchk]. destruct (Hcomp C HC) as [HCp [HCo HCt]].
        pose proof (Hlow p S st Hin Ens HlU) as Hnn.
        assert (Exl: gfinal_of U p = lower_bound st) by (rewrite Ef; unfold Constraints.final_value; rewrite Hnn; reflexivity).
        unfold gstatic_checked in Hchk. rewrite Hs in Hchk.
        assert (Hvb: vars_in (fun q => param_eqb q p || bound_b b q) S = true).
        { apply (vars_in_mono (bound_b b)); [intros q E; rewrite E; apply orb_true_r|].
          apply Hbound. apply (vars_in_mono _ _ (fun q E => proj2 (proj1 (andb_true_iff _ _) E)) _ Hsv). }
        pose proof (proj2 (Hchk Hnn) b Hpb Hbf Hnv (Hown _ Hql) Hvb Hsat C HC) as Hc'.
        rewrite Exl. destruct (ifrag env C) eqn:HCi.
        *
          rewrite (free_candidate env b p (lower_bound st) C Hpb (proj1 Hfl) (unmentioned b _ (proj1 Hfl) (Hown _ Hql))
              (ifrag_plain_variables p C HCi HCo)) in Hc'.
          rewrite (free_ext env _ b (with_value_same b p (lower_bound st) ltac:(rewrite (HlbO p S Hin), Exl; reflexivity)) C) in Hc'.
          exact Hc'.
        * (* a type variable of a mutability given to it, narrowed or made nullable, other than p *)
          destruct (pfrag_cases env C HCp) as [H|[[gm [nn [q [EC _]]]]|[gm [nn [q [EC _]]]]]]; [rewrite H in HCi; discriminate HCi| |];
              subst C; [rewrite (proj1 (candidate_reference env p _ gm nn q (HCt _ (or_introl eq_refl)))) in Hc'
                       |rewrite (proj2 (candidate_reference env p _ gm nn q (HCt _ (or_intror eq_refl)))) in Hc']; exact Hc'. }
    split.
    - intros p S Hin. split; [exact (Hqfin p S Hin)|exact (Hfinals p S Hin)].
    - (* the arguments: with the bindings *)
      assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf2 s -> unify env nf P A (Ongoing s) = Some (Ongoing s') ->
          gwf2 s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (instantiate_free env b P))).
      { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
        destruct (HPs P HP) as [HfP [HoP HvP]].
        destruct (mqparameter b Hpb Hbf gwf2 gwf2_capturable nf (fun k _ => gleaf_all k b)
            P A s s' HfP HoP (HPn P HP) Hnv (HAs A HA) Hs E) as [Hs' [Hn' Hsnd]].
        split; [exact Hs'|]. split; [exact Hn'|]. intros Hsb. exact (Hsnd Hsb (Hbound P HvP)). }
      destruct (mfold_chain gwf2 nf _ u U (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
          Hwfu Hfold) as [_ [_ Hall]].
      intros P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
      exact (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hsat)).
Qed.

End GenericArguments.

(* ---------------------------------------------------------------------------------------------- *)
(* Member calls, whatever the final values, with intersections as the types of parameters           *)
(* ---------------------------------------------------------------------------------------------- *)

Section AnyFinalValues.

Variable env: Environment.
Hypothesis wf: wellformed env.
Hypothesis intersect_no_vars: forall a b, no_vars a = true -> no_vars b = true -> no_vars (intersect env a b) = true.
Hypothesis supertype_no_vars: forall a b, no_vars a = true -> no_vars b = true ->
    no_vars (closest_common_supertype_with env a b) = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.

(* The conjectures of Conjectures.v *)
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis tame: tame_inheritance env.
Hypothesis intersect_in_fragment: intersect_stays_in_fragment env declared.
Hypothesis supertype_in_fragment: closest_common_supertype_stays_in_fragment env declared.
Hypothesis intersect_below: intersect_is_below_both env declared.
Hypothesis supertype_above: closest_common_supertype_is_above_both env declared.

(*
 * Calling a member function is sound, whatever the final values of its type parameters are, also where
 * the types of the parameters are intersections, as ofComponents makes their instances: as
 * FinalValues.member_call_with_any_final_values_sound, through member_call_in_generic_code_sound with no
 * type parameters of the caller. There, the final values are types of the fragment of Fragment.v, such
 * as intersections, which the components of the instance of an intersection are made of; and a type
 * variable made nullable in type arguments is narrowed, or of a non-null bound, as the compiler builds
 * `T?`, whose value, within the declared bound, isn't nullable.
 *)
Theorem member_call_with_any_final_values_and_intersections_sound:
    forall n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U,
    c <> nothing -> ca <> nothing -> e <> nothing ->
    map fst cvars = parameter_ids env c -> NoDup (map fst (cvars ++ ovars)) ->
    (forall p bound, In (p, bound) (cvars ++ ovars) -> in_fragment env bound = true) ->
    (* the bounds: the declared ones *)
    (forall p bound, In (p, bound) (cvars ++ ovars) -> to_generic bound = parameter_bound env p) ->
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
        exists o x f, z = TypeArgument Model.invariant o x /\ unify env f bound x (Ongoing []) = Some (Ongoing [])) ->
    (* the parameters, of the type parameters of c and of the function, and the arguments, accepted in turn *)
    (forall P, In P Ps -> qfrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (* the type variables made nullable in type arguments of the parameters: narrowed, or of non-null bounds *)
    (forall P, In P Ps -> args_narrowed env P = true) ->
    (forall A, In A As -> afrag env A = true /\ closed A = true) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hdecl Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HPn HAs Hfold b Hbdef P A HPA.
    assert (HAs': forall A, In A As -> of_fragment env declared A /\ bottom_only env A = true
        /\ owners_outside env (map fst (cvars ++ ovars)) A /\ True).
    { intros A' HA'. destruct (HAs A' HA') as [Ha HcA]. destruct (afrag_parts env A' Ha) as [Hf Hn].
      split; [exact (of_fragment_of_class env declared _ Hf)|]. split; [exact (class_bottom_only env A' Hf Hn)|].
      split; [exact (closed_owners_outside env _ A' Hf HcA)|exact I]. }
    destruct (member_call_in_generic_code_sound env wf intersect_no_vars supertype_no_vars declared declared_wf terminates finite
        tame intersect_in_fragment supertype_in_fragment intersect_below supertype_above
        (fun _ => True) (fun _ => True) (fun _ _ _ _ => I) (fun _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ => I) I I (fun _ => I)
        (fun _ _ _ _ _ _ => I) (fun _ _ => I) (fun _ _ => I) (fun _ _ => I) (fun _ _ _ _ => I)
        (fun _ _ _ _ _ _ _ _ _ _ => I)
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hdecl Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HPn HAs' (fun _ _ _ => I) Hfold) as [_ Hmain].
    destruct (Hmain b Hbdef) as [_ [_ [_ [_ Hsound]]]]. exact (Hsound P A HPA).
Qed.

End AnyFinalValues.

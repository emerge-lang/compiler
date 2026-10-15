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
Hypothesis not_expansive: non_expansive env.
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
Hypothesis Qb_root: forall m c args a, Qb (RootResolved m c args) -> In a args -> Qa a.
Hypothesis Qb_nullable: forall n, Qb (Nullable n) -> Qb n.
Hypothesis Qb_bound: forall g, Qb (Generic g) -> Qb (effective_bound env g).
Hypothesis Qb_narrowed: forall g, Qb (Generic g) -> Qb (without_null env (Generic g)).
Hypothesis Qb_component: forall cs c, Qb (Intersection cs) -> In c cs -> Qb c.
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
    destruct (terminates env declared wf declared_wf finite not_expansive y x [] Hy Hx Hry Hrx) as [n Hn].
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
    destruct (transitivity_terminating env wf declared declared_wf terminates finite not_expansive n1 n2 x y z Hx Hy Hz Hrx Hry Hrz)
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
    - apply andb_true_iff in Hf. destruct Hf as [_ Hcs]. simpl in Hn, Hr.
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
    - pose proof (gfrag_with_mutability env wf m _ Hf) as Hfm. rewrite <- (bottom_rest_with_mutability m) in Hr.
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
    destruct (gfrag_cases env A HA) as [[m [c [args ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]]; reflexivity.
Qed.

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
    destruct (is_nullable env _); [exact H|discriminate H].
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

(* The bounds of the variables not bound exactly are of Qb *)
Definition qstates (s: VariableStates): Prop :=
    forall p st, lookup_state s p = Some st -> is_exact st = false -> Qb (upper_bound st) /\ Qb (lower_bound st).

Definition gwf_states (s: VariableStates): Prop := wf_states env of_fragment of_fragment s /\ qstates s.

Lemma qstates_set: forall s p st, qstates s -> (is_exact st = false -> Qb (upper_bound st) /\ Qb (lower_bound st)) ->
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
    destruct (proj1 Hs p st Hl) as [Hnu [Hnl He]].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: its binding takes A *)
      destruct (keeps_free env wf n _ A s s' Hnl (of_fragment_no_vars A HA) H') as [-> _]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hlo in H'.
      exact (proj2 (gwrite_leaf n vb ob X o x A s s K HX Hx HA HbA Hc H')).
    - (* between bounds: the lower bound becomes the closest common supertype with A *)
      cbn zeta in H'.
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      pose proof (supertype_of_fragment _ _ Hbl HA) as Hfs.
      destruct (unify env n (upper_bound st) (closest_common_supertype_with env (lower_bound st) A) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free env wf n _ _ s ns Hnu (of_fragment_no_vars _ Hfs) E) as [-> H0].
      destruct (below_supertype _ _ Hbl HA) as [Hlo HAs].
      split; [|split].
      + destruct (proj2 Hs p st Hl Ee) as [Hqu Hql].
        split; [apply wf_set_state; [exact (proj1 Hs)|exact Hnu|exact (of_fragment_no_vars _ Hfs)|]|].
        * intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [exact Hbs|]. split; [exact Hbu|exact Hfs].
        * apply qstates_set; [exact (proj2 Hs)|]. intros _. split; [exact Hqu|exact (Qb_supertype _ _ Hbl HA Hql HqA)].
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
    destruct (proj1 Hs p st Hl) as [Hnu [Hnl He]].
    destruct (is_exact st) eqn:Ee.
    - (* bound exactly: A takes what its binding gives *)
      destruct (keeps_free env wf n A _ s s' (of_fragment_no_vars A HA) Hnu H') as [-> _]. split; [exact Hs|]. split; [auto|].
      intros o x Hx Hfit. specialize (Hfit st Hl). unfold gfits in Hfit. rewrite Ee in Hfit.
      destruct Hfit as [vb [ob [X [K [Hu [Hlo [HX [_ Hc]]]]]]]]. rewrite Hu in H'.
      exact (proj2 (gread_leaf n vb ob X o x A s s K HX Hx HA Hc H')).
    - (* between bounds: the upper bound becomes the intersection with A *)
      cbn zeta in H'.
      destruct (He eq_refl) as [Hcap [_ [Hbs [Hbu Hbl]]]].
      pose proof (intersect_of_fragment _ _ Hbu HA) as Hfi.
      destruct (is_non_nullable_nothing env (intersect env (upper_bound st) A)); [discriminate H'|].
      destruct (unify env n (intersect env (upper_bound st) A) (lower_bound st) (Ongoing s))
          as [[ns|]|] eqn:E; try discriminate H'. injection H' as <-.
      destruct (keeps_free env wf n _ _ s ns (of_fragment_no_vars _ Hfi) Hnl E) as [-> H0].
      destruct (intersect_below_both _ _ Hbu HA) as [Hiu HiA].
      split; [|split].
      + destruct (proj2 Hs p st Hl Ee) as [Hqu Hql].
        split; [apply wf_set_state; [exact (proj1 Hs)|exact (of_fragment_no_vars _ Hfi)|exact Hnl|]|].
        * intros _. split; [exact Hcap|]. split; [exists n; exact H0|]. split; [|split; [exact Hfi|exact Hbl]].
          intros x f Hx Ex. destruct (below_trans x _ _ Hx Hfi Hbu (ex_intro _ f Ex) Hiu) as [f1 E1]. exact (Hbs x f1 Hx E1).
        * apply qstates_set; [exact (proj2 Hs)|]. intros _. split; [exact (Qb_intersect _ _ Hbu HA Hqu HqA)|exact Hql].
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

Definition bindings_of_fragment: Prop :=
    forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> of_fragment x.

Lemma gsatisfies_of_fragment: forall s, gsatisfies b s -> bindings_of_fragment.
Proof. intros s H p o x E. exact (proj1 (H p o x E)). Qed.

(* The types of the parameters, instantiated, are of the fragment *)
Lemma instances_of_fragment: bindings_of_fragment -> forall k,
    (forall P, vsize P <= k -> ifrag env P = true -> bound_in env b K [] (to_generic P) = true -> of_fragment (inst env b P))
    /\ (forall a, vsize a <= k -> argument_ifrag env a = true -> bound_in env b K [] (to_generic a) = true ->
        argument_gfrag env (instantiate env b a) = true /\ refs_wf env declared (instantiate env b a)).
Proof.
    intros Hbf. induction k as [|k [IHt IHa]].
    - split.
      + intros P Hd HP HbP. destruct (ifrag_cases env wf P HP) as [[m [c [args [-> _]]]]|[->|[[m [c [args [-> _]]]]|[p [-> _]]]]];
            try (simpl in Hd; lia).
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p []) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        rewrite (inst_variable env b p [] _ _ _ Ex). exact (Hbf p o x Ex).
      + intros [| | | |v o n| |] Hd Ha; simpl in Ha; try discriminate Ha. simpl in Hd. lia.
    - assert (Hroot: forall m c args, ifrag env (RootResolved m c args) = true ->
          bound_in env b K [] (to_generic (RootResolved m c args)) = true -> vsize (RootResolved m c args) <= S k ->
          of_fragment (inst env b (RootResolved m c args))).
      { intros m c args HP HbP Hd. rewrite (inst_root env b m c args (ifrag_no_generics env _ HP)).
        assert (Hl: length args = length (parameter_ids env c)).
        { destruct (ifrag_cases env wf _ HP) as [[m' [c' [args' [Heq [_ [Hl _]]]]]]|[Heq|[[? [? [? [Heq _]]]]|[? [Heq _]]]]];
              try discriminate Heq.
          - injection Heq as <- <- <-. exact Hl.
          - unfold bottom_type in Heq. injection Heq as _ -> ->. rewrite (wf_nothing_has_no_type_parameters env wf). reflexivity. }
        assert (Hargs: forall a, In a args -> argument_gfrag env (instantiate env b a) = true /\ refs_wf env declared (instantiate env b a)).
        { intros a Ha. destruct (root_parts env wf b K [] m c args HP HbP a Ha) as [Hfa Hba].
          pose proof (vsize_below m c args a Ha). apply IHa; [lia|exact Hfa|exact Hba]. }
        split.
        - apply make_root_gfrag; [rewrite length_map; exact Hl|].
          intros a' Ha'. apply in_map_iff in Ha'. destruct Ha' as [a [<- Ha]]. exact (proj1 (Hargs a Ha)).
        - exact I. }
      split.
      + intros P Hd HP HbP. destruct (ifrag_shapes P HP) as [[m [c [args ->]]]|[[m [c [args [-> HP']]]]|[p [bnd ->]]]].
        * exact (Hroot m c args HP HbP Hd).
        * assert (Hb': bound_in env b K [] (to_generic (RootResolved m c args)) = true) by exact HbP.
          simpl in Hd. destruct (Hroot m c args HP' Hb' ltac:(simpl; lia)) as [Hg Hr].
          rewrite (inst_root env b m c args (ifrag_no_generics env _ HP')) in Hg, Hr.
          rewrite (inst_nullable env b m c args (ifrag_no_generics env _ HP')). split; [exact Hg|exact Hr].
        * destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) HbP) as [o [x [Ex _]]]. cbn [param_of] in Ex.
          rewrite (inst_variable env b p bnd _ _ _ Ex). exact (Hbf p o x Ex).
      + intros [| | | |v o n| |] Hd Ha HbA; simpl in Ha; try discriminate Ha. simpl in Hd.
        destruct (bound_in_argument env b K [] v o (to_generic n) HbA) as [_ Hbn].
        rewrite (instantiate_argument env wf b K [] v o n Ha Hbn). exact (IHt n ltac:(lia) Ha Hbn).
Qed.

Lemma instance_of_fragment: forall P, bindings_of_fragment -> ifrag env P = true -> bound_in env b K [] (to_generic P) = true ->
    of_fragment (inst env b P).
Proof. intros P Hbf HP Hb. exact (proj1 (instances_of_fragment Hbf (vsize P)) P (le_n _) HP Hb). Qed.

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
    rewrite unify_step_once in H. unfold unify_step, unify_intersection in H.
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
    (forall P A s s', ifrag env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> below A (inst env b P)))
    /\ (forall P A s s', ifrag env P = true -> yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> below (inst env b P) A))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> exists f, unify env f (instantiate env b P) A (Ongoing []) = Some (Ongoing [])))
    /\ (forall P A s s', argument_ifrag env P = true -> argument_yfrag b A -> bound_in env b K [] (to_generic P) = true ->
        gwf_states s -> unify env n A P (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
        /\ (gsatisfies b s' -> exists f, unify env f A (instantiate env b P) (Ongoing []) = Some (Ongoing []))).
Proof.
    induction n as [|n [IHt [IHa [IHat IHaa]]]].
    { split; [|split; [|split]]; intros P A s s'; repeat intros ?;
          match goal with H: unify env 0 _ _ _ = _ |- _ => discriminate H end. }
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
      intros P A s s' HP HA Hb Hs H.
      assert (Hroot: forall mt ct targs ma ca aargs, ifrag env (RootResolved mt ct targs) = true ->
          yfrag b (RootResolved ma ca aargs) -> bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true ->
          unify env (S n) (RootResolved mt ct targs) (RootResolved ma ca aargs) (Ongoing s) = Some (Ongoing s') ->
          gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> below (RootResolved ma ca aargs) (inst env b (RootResolved mt ct targs)))).
      { intros mt ct targs ma ca aargs Hft Hfa Hbt Hu.
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ Hft)).
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
          destruct (Htargs t Ht) as [Hft' Hbt']. exact (IHat t a s0 s0' Hft' (Hnorm' a Ha) Hbt' Hs0 E). }
        destruct (Hpairs targs norm s s' (instantiate env b) (fun a => a) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mt ct (map (instantiate env b) targs) targs), Hm, Hcn.
        exact Hf. }
      destruct (ifrag_shapes P HP) as [[mt [ct [targs ->]]]|[[mt [ct [targs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA Hb H).
        * rewrite unify_class_nullable in H. discriminate H.
        * (* a reference to a type parameter of the caller: by its bound *)
          rewrite step_root_generic in H.
          destruct (IHt _ _ s s' HP (yfrag_generic b _ HA) Hb Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP)) in Hf |- *.
          exists (S f). rewrite step_root_generic. exact Hf.
        * (* an intersection: through the component taken *)
          rewrite step_root_inter in H. destruct (flipped_some env n _ cs s s' H) as [c [Hc Ec]].
          destruct (yfrag_component b cs c HA Hc) as [Hyc _].
          destruct (IHt _ _ s s' HP Hyc Hb Hs Ec) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
          exact (below_trans _ c _ (yfrag_of_fragment b _ HA) (yfrag_of_fragment b c Hyc)
              (instance_of_fragment _ (gsatisfies_of_fragment s' Hsb) HP Hb)
              (intersection_below_component cs c (yfrag_of_fragment b _ HA) Hc) (Hsound Hsb)).
      + (* a nullable type: what it wraps *)
        rewrite (nullable_target n _ A s (proj1 (proj1 HA))) in H.
        assert (Hb': bound_in env b K [] (to_generic (RootResolved mt ct targs)) = true) by exact Hb.
        destruct (IHt _ _ s s' HP' (yfrag_nullable_assignee b A HA) Hb' Hs H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite (inst_nullable env b mt ct targs (ifrag_no_generics env _ HP')).
        rewrite (inst_root env b mt ct targs (ifrag_no_generics env _ HP')) in Hf.
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
      intros P A s s' HP HA Hb Hs H.
      assert (Hroot: forall ma ca aargs mp cp pargs, ifrag env (RootResolved mp cp pargs) = true ->
          yfrag b (RootResolved ma ca aargs) -> bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true ->
          unify env (S n) (RootResolved ma ca aargs) (RootResolved mp cp pargs) (Ongoing s) = Some (Ongoing s') ->
          gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s)
          /\ (gsatisfies b s' -> below (inst env b (RootResolved mp cp pargs)) (RootResolved ma ca aargs))).
      { intros ma ca aargs mp cp pargs Hfp Hfa Hbp Hu.
        rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ Hfp)).
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
        unfold unify_arguments in Hu.
        assert (Hp: forall t a, In (t, a) (combine aargs norm) -> forall s0 s0', gwf_states s0 ->
            unify env n t a (Ongoing s0) = Some (Ongoing s0') ->
            gwf_states s0' /\ (forall b', gsatisfies b' s0' -> gsatisfies b' s0)
            /\ (gsatisfies b s0' -> exists f, unify env f ((fun a => a) t) (instantiate env b a) (Ongoing []) = Some (Ongoing []))).
        { intros t a Hin s0 s0' Hs0 E. apply in_combine_l in Hin as Ht. apply in_combine_r in Hin as Ha.
          destruct (Hnormp a Ha) as [Hfa' Hba']. exact (IHaa a t s0 s0' Hfa' (Haargs t Ht) Hba' Hs0 E). }
        destruct (Hpairs aargs norm s s' (fun a => a) (instantiate env b) Hp Hs Hu) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
        rewrite map_id in Hf. exists (S f).
        rewrite unify_classes, Hbase, (assignment_mutability_of_class env mp cp (map (instantiate env b) pargs) pargs), Hm, Hcn.
        unfold unify_arguments. rewrite Hcomm. exact Hf. }
      destruct (ifrag_shapes P HP) as [[mp [cp [pargs ->]]]|[[mp [cp [pargs [-> HP']]]]|[p [bnd ->]]]].
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * exact (Hroot _ _ _ _ _ _ HP HA Hb H).
        * rewrite unify_nullable_class in H.
          destruct (IHa _ _ s s' HP (proj1 (yfrag_nullable b an HA)) Hb Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)) in Hf |- *. exists (S f). rewrite unify_nullable_class. exact Hf.
        * (* a reference to a type parameter of the caller takes Nothing only *)
          rewrite step_generic_root in H.
          destruct (is_non_nullable_nothing env (RootResolved mp cp pargs) && _) eqn:Ec; [|discriminate H].
          injection H as <-. split; [exact Hs|]. split; [auto|]. intros _. exists 1.
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)), step_generic_root.
          cbn [is_non_nullable_nothing assignment_mutability] in Ec |- *. rewrite Ec. reflexivity.
        * (* an intersection: each of its components takes it *)
          destruct (intersection_takes (fun c => below (inst env b (RootResolved mp cp pargs)) c) n cs mp cp pargs s s'
              (gfrag_components_no_vars env cs (proj1 (proj1 HA))) H) as [Hs' [Hext Hall]];
              [|exact Hs|].
          { intros c s0 s0' Hc Hs0 E. exact (IHa _ c s0 s0' HP (proj1 (yfrag_component b cs c HA Hc)) Hb Hs0 E). }
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
          pose proof (instance_of_fragment _ (gsatisfies_of_fragment s' Hsb) HP Hb) as HiP.
          apply (below_intersection_of _ cs HiP (yfrag_of_fragment b _ HA)); [|exact (Hall Hsb)].
          rewrite (inst_root env b _ _ _ (ifrag_no_generics env _ HP)). reflexivity.
      + destruct (gfrag_cases env A (proj1 (proj1 HA))) as [[ma [ca [aargs ->]]]|[[an [-> _]]|[[gm [nn [q [bq [-> _]]]]]|[cs ->]]]].
        * rewrite unify_class_nullable in H. discriminate H.
        * rewrite unify_nullable_nullable in H.
          assert (Hb': bound_in env b K [] (to_generic (RootResolved mp cp pargs)) = true) by exact Hb.
          destruct (IHa _ _ s s' HP' (proj1 (yfrag_nullable b an HA)) Hb' Hs H) as [Hs' [Hext Hsound]].
          split; [exact Hs'|]. split; [exact Hext|]. intros Hsb. destruct (Hsound Hsb) as [f Hf].
          rewrite (inst_root env b mp cp pargs (ifrag_no_generics env _ HP')) in Hf.
          rewrite (inst_nullable env b mp cp pargs (ifrag_no_generics env _ HP')).
          exists (S f). rewrite unify_nullable_nullable. exact Hf.
        * rewrite step_generic_nullable in H. discriminate H.
        * rewrite step_inter_nullable in H. discriminate H.
      + (* a type variable *)
        destruct (gassignee_leaf n p bnd A s s' Hs (proj1 HA) (proj2 (proj2 (proj2 HA))) H) as [Hs' [Hext Hsound]].
        split; [exact Hs'|]. split; [exact Hext|]. intros Hsb.
        destruct (binds_ref_some env wf b K [] (mkGenericRef None false p bnd) Hb) as [o [x [Ex _]]]. cbn [param_of] in Ex.
        destruct (Hsb p o x Ex) as [Hx [st' [Hl' Hfit]]].
        assert (Hfits: forall st'', lookup_state s' p = Some st'' -> gfits st'' o x)
            by (intros st'' Hl''; rewrite Hl' in Hl''; injection Hl'' as <-; exact Hfit).
        rewrite (inst_variable env b p bnd _ _ _ Ex). exact (Hsound o x Hx Hfits).
    - (* a type argument with type variables as the target *)
      intros [| | | |vt ot nt| |] [| | | |va oa na| |] s s' HP HA Hb Hs H; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument b va oa na HA) as [HAn Hoa].
      destruct (bound_in_argument env b K [] vt ot (to_generic nt) Hb) as [_ Hbn].
      rewrite (unify_type_arguments_exact env s n vt ot nt va oa na (not_capturable env of_fragment of_fragment s nt (proj1 Hs))) in H.
      destruct (ownership_is_assignable_to oa ot) eqn:Ho; [|discriminate H].
      pose proof (ownership_kept b oa ot Ho Hoa) as Hown.
      assert (Hfi: is_type_variable (inst env b nt) = false)
          by exact (instance_not_variable env wf b K [] (to_generic nt) (ifrag_sfrag env nt HP) Hbn).
      assert (Hgoal: forall f, compare_variances (unify env f) vt va (inst env b nt) na [] = Some (Ongoing []) ->
          unify env (S f) (instantiate env b (TypeArgument vt ot nt)) (TypeArgument va oa na) (Ongoing []) = Some (Ongoing [])).
      { intros f E. rewrite (instantiate_argument env wf b K [] vt ot nt HP Hbn).
        rewrite (unify_type_arguments env f vt _ (inst env b nt) va oa na [] Hfi), Hown. exact E. }
      destruct vt, va; unfold compare_variances in H; try discriminate H.
      1: { destruct (unify env n nt na (Ongoing s)) as [[s1|]|] eqn:E1; [|rewrite unify_keeps_failure in H; discriminate H|discriminate H].
           destruct (IHt nt na s s1 HP HAn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHa nt na s1 s' HP HAn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHt nt na s s' HP HAn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt na s s' HP HAn Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHt nt top_type s s' HP (yfrag_top b) Hbn Hs H) as [Hs' [Hext Hsnd]]
          | destruct (IHa nt bottom_type s s' HP (yfrag_bottom b) Hbn Hs H) as [Hs' [Hext Hsnd]] ];
          split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
          exists (S f); apply Hgoal; unfold compare_variances; exact Hf.
    - (* a type argument with type variables as the assignee *)
      intros [| | | |vp op np| |] [| | | |va oa na| |] s s' HP HA Hb Hs H; try discriminate HP;
          try (destruct HA as [HA _]; simpl in HA; discriminate HA).
      simpl in HP. destruct (yfrag_argument b va oa na HA) as [HAn Hoa].
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
           destruct (IHa np na s s1 HP HAn Hbn Hs E1) as [Hs1 [Hext1 Hsnd1]].
           destruct (IHt np na s1 s' HP HAn Hbn Hs1 H) as [Hs' [Hext2 Hsnd2]].
           split; [exact Hs'|]. split; [intros b' Hb'; apply Hext1, Hext2, Hb'|]. intros Hsb.
           destruct (Hsnd2 Hsb) as [f2 Hf2]. destruct (Hsnd1 (Hext2 b Hsb)) as [f1 Hf1].
           exists (S (max f1 f2)). apply Hgoal. unfold compare_variances.
           rewrite (unify_fuel_monotone env f1 (max f1 f2) _ _ _ _ ltac:(lia) Hf1).
           exact (unify_fuel_monotone env f2 (max f1 f2) _ _ _ _ ltac:(lia) Hf2). }
      all: first
          [ destruct (IHa np na s s' HP HAn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | destruct (IHt np na s s' HP HAn Hbn Hs H) as [Hs' [Hext Hsnd]];
            split; [exact Hs'|]; split; [exact Hext|]; intros Hsb; destruct (Hsnd Hsb) as [f Hf];
            exists (S f); apply Hgoal; unfold compare_variances; exact Hf
          | (* no type variables involved *)
            match type of H with unify env ?k ?x ?y _ = _ =>
              destruct (keeps_free env wf k x y s s' ltac:(first [exact Hnna|reflexivity]) ltac:(first [exact Hnna|reflexivity]) H)
                  as [-> H0];
              split; [exact Hs|]; split; [auto|]; intros _; exists (S k); apply Hgoal; unfold compare_variances; exact H0
            end ].
Qed.

End Main.

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
    gwf_states s0 ->
    (forall P, In P Ps -> ifrag env P = true /\ bound_in env b K [] (to_generic P) = true) ->
    (forall A, In A As -> yfrag b A) ->
    fold_unify (fun inner '(P, A) => unify env n P A inner) (combine Ps As) (Ongoing s0) = Some (Ongoing u) ->
    gwf_states u /\ (gsatisfies b u -> forall P A, In (P, A) (combine Ps As) -> below A (inst env b P)).
Proof.
    intros n Ps As s0 u b K Hs0 HPs HAs H.
    assert (Hstep: forall P A, In (P, A) (combine Ps As) -> forall s s', gwf_states s ->
        unify env n P A (Ongoing s) = Some (Ongoing s') ->
        gwf_states s' /\ (forall b', gsatisfies b' s' -> gsatisfies b' s) /\ (gsatisfies b s' -> below A (inst env b P))).
    { intros P A Hin s s' Hs E. apply in_combine_l in Hin as HP. apply in_combine_r in Hin as HA.
      destruct (HPs P HP) as [HfP HbP]. exact (proj1 (generic_arguments b K n) P A s s' HfP (HAs A HA) HbP Hs E). }
    destruct (gfold_chain n _ s0 u (fun P A Hin s s' Hs E => let H' := Hstep P A Hin s s' Hs E in conj (proj1 H') (proj1 (proj2 H')))
        Hs0 H) as [Hu [_ Hall]].
    split; [exact Hu|]. intros Hb P A Hin. destruct (Hall P A Hin) as [s [s' [Hs [E Hx]]]].
    exact (proj2 (proj2 (Hstep P A Hin s s' Hs E)) (Hx b Hb)).
Qed.

(* The final value of a variable that isn't bound exactly is within its bounds *)
Lemma generic_final_value_fits: forall s p st o, gwf_states s -> lookup_state s p = Some st -> is_exact st = false ->
    of_fragment (Constraints.final_value env st) -> gfits st o (Constraints.final_value env st).
Proof.
    intros s p st o Hs Hl He Hf. destruct (proj1 Hs p st Hl) as [_ [_ Hb]]. destruct (Hb He) as [_ [[K HK] _]].
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
    (forall P, In P Ps -> ifrag env P = true /\ refs_within env (cvars ++ ovars) P) ->
    (forall A, In A As -> of_fragment A /\ bottom_only A = true /\ owners_outside (map fst (cvars ++ ovars)) A /\ Qb A) ->
    (forall p bound, In (p, bound) ovars -> Qb bound) ->
    fold_unify (fun inner '(P, A) => unify env nf P A inner) (combine Ps As) (Ongoing u) = Some (Ongoing U) ->
    (* the final values are of Qb *)
    (forall p bound, In (p, bound) ovars -> Qb (final_value_of env U p))
    /\ forall b, b = bindings_of env c zs ++ map (fun v => (fst v, TypeArgument Model.invariant ref (final_value_of env U (fst v)))) ovars ->
    (* the types of the parameters are bound in b, which binds the type parameters of c to the type
       arguments of the object, and those of the function to their final values *)
    (exists K, forall P, In P Ps -> bound_in env b K [] (to_generic P) = true)
    /\ (forall p o x, lookup_binding b p = Some (TypeArgument Model.invariant o x) -> is_exact_ownership o = true
        /\ (In (TypeArgument Model.invariant o x) zs \/ exists bound, In (p, bound) ovars /\ x = final_value_of env U p))
    /\ forall P A, In (P, A) (combine Ps As) -> exists f, is_assignable_to env f A (inst env b P) = Some true.
Proof.
    intros n mr c cvars ovars ma ca ys u mo e xs zs n0 Ps As nf U Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hxx Hzb
        HPs HAs HQbounds Hfold.
    pose proof (object_arguments_exact env wf c mo e xs zs He (object_below env wf n mr c _ ma ca ys _ u mo e xs n0 Hrec Hobj) Hfo Hxx Hzs)
        as Hzx.
    destruct (receiver_and_object env wf of_fragment of_fragment generic_inference_types
        n mr c cvars ovars ma ca ys u mo e xs zs n0 Hc Hca He Hids Hnd Hbounds Hfy Hrec Hfo Hobj Hzs Hzx)
        as [ys' [n1 [Hl [Hlz [Hys [Hcap [Hownu [Hwfu0 [Hp Hrest]]]]]]]]].
    assert (Hwfu: gwf_states u).
    { split; [exact Hwfu0|]. intros p st Hl' He'. destruct (Hrest p st Hl' He') as [bound [Hin ->]].
      split; [exact (HQbounds p bound Hin)|exact Qb_bottom]. }
    pose proof Hnd as Hnd'. rewrite map_app in Hnd.
    set (vars := cvars ++ ovars) in *.
    (* the arguments, as the types of the arguments of the bindings over vars *)
    assert (HAs': forall b', (forall q, ~ In q (map fst vars) -> lookup_binding b' q = None) -> forall A, In A As -> yfrag b' A).
    { intros b' Hb' A HA. destruct (HAs A HA) as [Hf [Hbo [Ho Hq]]]. split; [exact Hf|]. split; [exact Hbo|].
      split; [exact (owners_outside_free _ b' Hb' A Ho)|exact Hq]. }
    (* the variable states unify ends with, with the bounds themselves for the type parameters *)
    set (b0 := map (fun v => (fst v, TypeArgument Model.invariant ref (snd v))) vars).
    destruct (uniform_fuel_list vars (fun f v => unify env f (snd v) (snd v) (Ongoing []) = Some (Ongoing [])))
        as [K0 HK0].
    { intros f f' v Hle E. exact (unify_fuel_monotone env f f' _ _ _ _ Hle E). }
    { intros [p bound] Hin. exists (depth bound).
      exact (proj1 (reflexivity_with_arguments env (depth bound)) bound [] (Hbounds p bound Hin) (le_n _)). }
    assert (Hb0: forall P, In P Ps -> bound_in env b0 K0 [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs env wf vars _ _ P (or_introl (proj1 (HPs P HP))) (proj2 (HPs P HP))).
      - intros p bound Hin. unfold binds_exactly, b0. rewrite (lookup_map_vars vars _ p bound Hnd' Hin). cbn [snd].
        rewrite (in_fragment_is_gfrag env _ (Hbounds p bound Hin)). unfold respects. pose proof (HK0 (p, bound) Hin) as E0.
        cbn [snd] in E0. rewrite E0. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        simpl. unfold b0. rewrite (lookup_map_vars vars _ q bound Hnd' Hin). reflexivity. }
    destruct (generic_invocation_sound nf Ps As u U b0 K0 Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb0 P HP))
        (HAs' b0 (fun q Hq => lookup_map_none vars _ q Hq)) Hfold) as [HwfU _].
    destruct (fold_keeps_exact_unify env nf _ u U Hfold) as [Hkeep Hkeep2].
    assert (Hfinal': forall p bound, In (p, bound) ovars -> of_fragment (final_value_of env U p)).
    { intros p bound Hin.
      destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (proj1 HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [_ [Hbu Hbl]]]].
      unfold final_value_of, Constraints.final_value. rewrite HlU. destruct (is_non_nullable_nothing env (lower_bound st2)); assumption. }
    split.
    { intros p bound Hin. destruct (Hkeep2 p _ (Hownu p bound Hin) eq_refl eq_refl) as [st2 [HlU [He2 _]]].
      destruct (proj2 HwfU p st2 HlU He2) as [Hqu Hql].
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
      destruct (proj1 HwfU p st2 HlU) as [_ [_ Hw]]. destruct (Hw He2) as [_ [_ [Hbs _]]].
      unfold gfits in Hfit. rewrite He2 in Hfit. destruct Hfit as [_ [K2 E2]].
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
        rewrite (lookup_map_vars ovars (fun v => TypeArgument Model.invariant ref (final_value_of env U (fst v))) p bound Hndo Hin).
        cbn [fst]. exists ref, (final_value_of env U p). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (proj1 (Hfinal' p bound Hin))|].
        destruct (Hfin p bound Hin) as [st [_ [_ [-> [_ Ef]]]]]. exact Ef. }
    destruct (uniform_fuel_list vars (fun f v => forall o x, lookup_binding b (fst v) = Some (TypeArgument Model.invariant o x) ->
        unify env f (snd v) x (Ongoing []) = Some (Ongoing []))) as [K HK].
    { intros f f' v Hle E o x Hx. exact (unify_fuel_monotone env f f' _ _ _ _ Hle (E o x Hx)). }
    { intros [p bound] Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [_ [_ [f Ef]]]]]].
      exists f. intros o' x' Hx'. cbn [fst snd] in Hx' |- *. rewrite Hl' in Hx'. injection Hx' as <- <-. exact Ef. }
    assert (Hb: forall P, In P Ps -> bound_in env b K [] (to_generic P) = true).
    { intros P HP. apply (bound_in_from_refs env wf vars _ _ P (or_introl (proj1 (HPs P HP))) (proj2 (HPs P HP))).
      - intros p bound Hin. destruct (Hlookup p bound Hin) as [o [x [Hl' [Ho [Hx _]]]]].
        unfold binds_exactly. rewrite Hl', Ho, Hx. unfold respects. pose proof (HK (p, bound) Hin o x Hl') as E1.
        cbn [snd] in E1. rewrite E1. reflexivity.
      - intros q Hq. apply in_map_iff in Hq. destruct Hq as [[q' bound] [Hfst Hin]]. simpl in Hfst. subst q'.
        destruct (Hlookup q bound Hin) as [o [x [Hl' [Ho _]]]]. simpl. rewrite Hl'. exact Ho. }
    (* the type parameters of the caller are none of those inferred *)
    assert (Hbnone: forall q, ~ In q (map fst vars) -> lookup_binding b q = None).
    { intros q Hq. rewrite Hbdef, lookup_app.
      assert (Hnc: ~ In q (parameter_ids env c)).
      { rewrite <- Hids. intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. left. exact Hin. }
      rewrite (lookup_combine_none _ zs q Hnc: lookup_binding (bindings_of env c zs) q = None).
      apply (lookup_map_none ovars (fun v => TypeArgument Model.invariant ref (final_value_of env U (fst v))) q).
      intros Hin. apply Hq. unfold vars. rewrite map_app. apply in_or_app. right. exact Hin. }
    destruct (generic_invocation_sound nf Ps As u U b K Hwfu (fun P HP => conj (proj1 (HPs P HP)) (Hb P HP))
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
    intros P A HPA. destruct (Hsound Hsat P A HPA) as [f Ef].
    exists f. unfold is_assignable_to, empty_unification. rewrite Ef. reflexivity.
Qed.

End GenericArguments.

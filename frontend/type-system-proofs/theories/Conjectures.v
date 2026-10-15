From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import States.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Fragment.
From EmergeTypeSystem Require Import Generics.
From Stdlib Require Import List Arith.
Import ListNotations.

(* ---------------------------------------------------------------------------------------------- *)
(* Conjectures about the Kotlin implementation                                                      *)
(*                                                                                                *)
(* The model takes some functions of the frontend as given, as fields of the Environment, rather    *)
(* than defining them: BoundIntersectionTypeReference.intersect and closestCommonSupertypeWith       *)
(* among them. What the proofs need of them is stated here, unproven: each conjecture is a property *)
(* of an environment, and a theorem that needs one takes it as a premise.                           *)
(*                                                                                                *)
(* They can't be axioms. The functions being fields of Environment, Rocq lets them be anything, so   *)
(* each conjecture is false of some environment; as an axiom over all environments, it would let     *)
(* Rocq prove anything. They are claims about the one environment of the Kotlin implementation.     *)
(*                                                                                                *)
(* The types are those of Generics.v: of the fragment gfrag. A conjecture whose inputs are outside *)
(* of it claims nothing about them.                                                               *)
(*                                                                                                *)
(* One conjecture is about the model alone: that unify terminates where inheritance isn't          *)
(* expansive (unify_terminates, below). It is a claim about every such environment, a theorem to   *)
(* prove rather than a property to check of the Kotlin implementation.                            *)
(* ---------------------------------------------------------------------------------------------- *)

Section Conjectures.

Variable env: Environment.
Variable declared: TypeParameterId -> EType.

Let in_gfrag (t: EType): Prop := gfrag env t = true /\ refs_wf env declared t.

(* BoundIntersectionTypeReference.intersect builds types of the fragment: it flattens intersections,
   nullable ones too, and makes them with ofComponents. *)
Definition intersect_stays_in_fragment: Prop :=
    forall a b, in_gfrag a -> in_gfrag b -> in_gfrag (intersect env a b).

(* closestCommonSupertypeWith builds types of the fragment: of class types, the common supertype
   with the type arguments combined by BoundTypeArgument.intersect; of a reference to a type
   parameter, that reference or the common supertype of its bound; of an intersection, the
   intersection of the common supertypes of its components. *)
Definition closest_common_supertype_stays_in_fragment: Prop :=
    forall a b, in_gfrag a -> in_gfrag b -> in_gfrag (closest_common_supertype_with env a b).

(* The intersection of two types is assignable to each of them. Like all of unify, deciding that may
   not terminate in general (see transitivity_never_fails in Generics.v); this claims it does. *)
Definition intersect_is_below_both: Prop :=
    forall a b, in_gfrag a -> in_gfrag b ->
        (exists n, is_assignable_to env n (intersect env a b) a = Some true)
        /\ (exists n, is_assignable_to env n (intersect env a b) b = Some true).

(* Each of two types is assignable to their closest common supertype; likewise. *)
Definition closest_common_supertype_is_above_both: Prop :=
    forall a b, in_gfrag a -> in_gfrag b ->
        (exists n, is_assignable_to env n a (closest_common_supertype_with env a b) = Some true)
        /\ (exists n, is_assignable_to env n b (closest_common_supertype_with env a b) = Some true).

End Conjectures.

(* ---------------------------------------------------------------------------------------------- *)
(* What follows from them, by transitivity: the bounds of type variables are bounds. These are the  *)
(* hypotheses intersect_is_below and supertype_is_above of Constraints.v, for the types of the      *)
(* fragment of Generics.v, where transitivity is that unify never rejects.                         *)
(* ---------------------------------------------------------------------------------------------- *)

Section Bounds.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Let declared_gfrag := bw_gfrag env declared declared_wf.

Let in_gfrag (t: EType): Prop := gfrag env t = true /\ refs_wf env declared t.

Let transitive := transitivity_never_fails env wf declared declared_wf.

(* What is assignable to the intersection of two types, unify never rejects for each of them *)
Theorem below_intersection_never_fails:
    intersect_stays_in_fragment env declared -> intersect_is_below_both env declared ->
    forall a b x n, in_gfrag a -> in_gfrag b -> in_gfrag x ->
        is_assignable_to env n x (intersect env a b) = Some true ->
        forall f, is_assignable_to env f x a <> Some false /\ is_assignable_to env f x b <> Some false.
Proof.
    intros Hfrag Hbelow a b x n Ha Hb Hx H f.
    destruct (Hfrag a b Ha Hb) as [Hi Hri]. destruct (Hbelow a b Ha Hb) as [[na Hna] [nb Hnb]].
    split.
    - exact (transitive n na x _ a (proj1 Hx) Hi (proj1 Ha) (proj2 Hx) Hri (proj2 Ha) H Hna f).
    - exact (transitive n nb x _ b (proj1 Hx) Hi (proj1 Hb) (proj2 Hx) Hri (proj2 Hb) H Hnb f).
Qed.

(* What the closest common supertype of two types is assignable to, unify never rejects for each of them *)
Theorem above_closest_common_supertype_never_fails:
    closest_common_supertype_stays_in_fragment env declared -> closest_common_supertype_is_above_both env declared ->
    forall a b x n, in_gfrag a -> in_gfrag b -> in_gfrag x ->
        is_assignable_to env n (closest_common_supertype_with env a b) x = Some true ->
        forall f, is_assignable_to env f a x <> Some false /\ is_assignable_to env f b x <> Some false.
Proof.
    intros Hfrag Habove a b x n Ha Hb Hx H f.
    destruct (Hfrag a b Ha Hb) as [Hs Hrs]. destruct (Habove a b Ha Hb) as [[na Hna] [nb Hnb]].
    split.
    - exact (transitive na n a _ x (proj1 Ha) Hs (proj1 Hx) (proj2 Ha) Hrs (proj2 Hx) Hna H f).
    - exact (transitive nb n b _ x (proj1 Hb) Hs (proj1 Hx) (proj2 Hb) Hrs (proj2 Hx) Hnb H f).
Qed.

End Bounds.

(* ---------------------------------------------------------------------------------------------- *)
(* Termination                                                                                    *)
(*                                                                                                *)
(* unify isn't known to terminate on all types: with expansive inheritance and contravariance, as *)
(* in `interface N<Z> : C<in N<N<Z>>>`, checking subtyping can go on forever (Kennedy and Pierce, *)
(* "On Decidability of Nominal Subtyping with Variance"). The frontend rejects expansive          *)
(* inheritance (findExpansiveSupertypes, in compiler/binding/basetype/ExpansiveInheritance.kt).   *)
(* Kennedy and Pierce show subtyping decidable without it; that unify terminates then is          *)
(* conjectured here, for a program's finite class table (unify_terminates).                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* The type parameters a type mentions, each with whether nested in a type argument of a class type
   in it; not those in the bounds of references *)
Fixpoint parameter_occurrences (nested: bool) (t: EType): list (TypeParameterId * bool) :=
    match t with
    | Generic (mkGenericRef _ _ p _) => [(p, nested)]
    | RootResolved _ _ arguments => flat_map (parameter_occurrences true) arguments
    | TypeArgument _ _ n => parameter_occurrences nested n
    | Nullable n => parameter_occurrences nested n
    | Intersection components => flat_map (parameter_occurrences nested) components
    | _ => []
    end.

(* The class types in a type, with their type arguments *)
Fixpoint constructed_types (t: EType): list (Class * list EType) :=
    match t with
    | RootResolved _ c arguments => (c, arguments) :: flat_map constructed_types arguments
    | TypeArgument _ _ n => constructed_types n
    | Nullable n => constructed_types n
    | Intersection components => flat_map constructed_types components
    | _ => []
    end.

Section Expansive.

Variable env: Environment.

(* An edge from p to the j-th type parameter q of a class c, wherever p is in the j-th type argument of
   c in a supertype of a class; expansive where p is nested deeper in it. Taken over all supertypes,
   the templates of which compose those declared, this has a cycle with an expansive edge where the
   one of findExpansiveSupertypes over the declared supertypes has. *)
Definition inheritance_edge (p q: TypeParameterId) (expansive: bool): Prop :=
    exists sub super c arguments j a,
        sub <> super /\ sub <> nothing /\ base_type_is_subtype_of env sub super = true
        /\ In (c, arguments) (constructed_types (RootResolved None super (supertype_arguments env sub super)))
        /\ nth_error arguments j = Some a /\ nth_error (parameter_ids env c) j = Some q
        /\ In (p, expansive) (parameter_occurrences false a).

(* No cycle has an expansive edge: there is a rank that no edge increases and every expansive one
   decreases *)
Definition non_expansive: Prop :=
    exists rank: TypeParameterId -> nat, forall p q expansive, inheritance_edge p q expansive ->
        if expansive then rank q < rank p else rank q <= rank p.

(* Finitely many classes have supertypes with type arguments *)
Definition finitely_many_templates: Prop :=
    exists classes: list Class, forall sub super, supertype_arguments env sub super <> [] -> In sub classes.

End Expansive.

(*
 * unify terminates on the types of the fragment of Generics.v, where inheritance isn't expansive, as
 * ExpansiveInheritance.kt makes sure.
 *
 * Why this stays a conjecture: Kennedy and Pierce show the goals reachable from a query finite where
 * inheritance isn't expansive, for a much smaller calculus. Here no size of the types decreases:
 * normalizing an assignee to a supertype grows its type arguments (`B<E> : A<Box<E>>`), and an
 * in-variant type argument swaps target and assignee. A measure would have to come from the rank of
 * non_expansive, and cover effective bounds, intersections, nullability and Nothing as well. That
 * declared supertypes have no variance on their type arguments (wf_supertypes_are_exact) helps:
 * inheritance alone brings in no contravariance, which their undecidable examples rest on; `in`
 * comes only from the types written, or nested in the type arguments of supertypes.
 *
 * What it would take if it didn't hold: where the frontend runs unify, it would not finish (a stack
 * overflow), and so reject a program, never accept one. The theorems resting on it, though, are about
 * unifications the frontend never runs: of the instances of generic code (SubstitutionTerminating.v,
 * SubstitutionWide.v) and of the final values of inference (FinalValues.v). For those, unify never
 * rejecting is proven without it (transitivity_never_fails, instances_never_fail); what rests on it is
 * that unify also accepts. A unification that neither fails nor ends is a derivation in the
 * coinductive reading of subtyping, which Kennedy and Pierce discuss, and which suits nominal types;
 * so this would be a gap in the proof, not a known way for an unsound program to be accepted.
 *)
Definition unify_terminates: Prop :=
    forall env declared,
        wellformed env ->
        bounds_wellformed env declared ->
        finitely_many_templates env -> non_expansive env ->
        forall t a s, gfrag env t = true -> gfrag env a = true -> refs_wf env declared t -> refs_wf env declared a ->
            exists n, unify env n t a (Ongoing s) <> None.

Section Terminating.

Variable env: Environment.
Hypothesis wf: wellformed env.
Let ranked := wf_bounds_ranked env wf.
Let supertypes_mention_no_variables := wf_supertypes_mention_no_variables env wf.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_wf: bounds_wellformed env declared.
Let declared_gfrag := bw_gfrag env declared declared_wf.
Hypothesis terminates: unify_terminates.
Hypothesis finite: finitely_many_templates env.
Hypothesis not_expansive: non_expansive env.

(* Transitivity, as usual, where unify terminates *)
Theorem transitivity_terminating: forall n1 n2 x y z,
    gfrag env x = true -> gfrag env y = true -> gfrag env z = true ->
    refs_wf env declared x -> refs_wf env declared y -> refs_wf env declared z ->
    is_assignable_to env n1 x y = Some true -> is_assignable_to env n2 y z = Some true ->
    exists f, is_assignable_to env f x z = Some true.
Proof.
    intros n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2.
    destruct (terminates env declared wf declared_wf finite not_expansive
        z x [] Hz Hx Hrz Hrx) as [f Hf].
    exists f. pose proof (transitivity_never_fails env wf declared declared_wf
        n1 n2 x y z Hx Hy Hz Hrx Hry Hrz H1 H2 f) as Hnf.
    unfold is_assignable_to, empty_unification in *.
    destruct (unify env f z x (Ongoing [])) as [[u|]|]; simpl in *; [reflexivity|contradiction Hnf; reflexivity|contradiction Hf; reflexivity].
Qed.

End Terminating.

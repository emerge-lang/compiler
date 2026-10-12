From EmergeTypeSystem Require Import Model.
From EmergeTypeSystem Require Import Subtyping.
From EmergeTypeSystem Require Import Transitivity.
From EmergeTypeSystem Require Import Constraints.
From EmergeTypeSystem Require Import Generics.
From Stdlib Require Import List.

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
(* The types are those of Generics.v: of the fragment gfrag, with the references to type parameters *)
(* well-formed (refs_wf). A conjecture whose inputs are outside of it claims nothing about them.     *)
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
Hypothesis supertypes_mention_no_variables: forall sub super t,
    In t (supertype_arguments env sub super) -> no_vars t = true.
Variable declared: TypeParameterId -> EType.
Hypothesis declared_gfrag: forall p, gfrag env (declared p) = true.
Hypothesis declared_mutability: forall p m, mutability_of env (with_mutability env m (declared p)) = m.

Let in_gfrag (t: EType): Prop := gfrag env t = true /\ refs_wf env declared t.

Let transitive := transitivity_never_fails env wf supertypes_mention_no_variables declared declared_gfrag declared_mutability.

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

From Stdlib Require Import String Arith.

Section Model.

Inductive Mutability :=
    | exclusive
    | immutable
    | readonly
    | mutable
    .

Scheme Equality for Mutability.

Definition is_subtype_of (src tgt: Mutability): bool :=
    match src, tgt with
    | exclusive, _ => true
    | immutable, immutable => true
    | immutable, readonly => true
    | mutable, mutable => true
    | mutable, readonly => true
    | readonly, readonly => true
    | _, _ => false
    end.

Definition union (a b: Mutability): Mutability :=
    if Mutability_beq a b then a else
    if Mutability_beq a exclusive then b else
    if Mutability_beq b exclusive then a else
    readonly
    .

Theorem union_comm: forall a b: Mutability, union a b = union b a.
Proof.
    intros [] []; reflexivity.
Qed.

Theorem union_assoc: forall a b c: Mutability, union (union a b) c = union a (union b c).
Proof.
    intros [] [] []; reflexivity.
Qed.

Definition intersect_mutability (a b: Mutability): Mutability :=
    match a, b with
    | mutable, mutable => mutable
    | mutable, readonly => mutable
    | mutable, immutable => exclusive
    | mutable, exclusive => exclusive
    | readonly, readonly => readonly
    | readonly, immutable => immutable
    | readonly, mutable => mutable
    | readonly, exclusive => exclusive
    | immutable, immutable => immutable
    | immutable, exclusive => exclusive
    | immutable, readonly => immutable
    | immutable, mutable => exclusive
    | exclusive, _ => exclusive
    end.

Theorem intersect_mutability_comm: forall a b: Mutability, intersect_mutability a b = intersect_mutability b a.
Proof.
    intros [] []; reflexivity.
Qed.

Theorem intersect_mutability_assoc: forall a b c: Mutability, intersect_mutability (intersect_mutability a b) c = intersect_mutability a (intersect_mutability b c).
Proof.
    intros [] [] []; reflexivity.
Qed.

Definition mutability_allows_mutation (m: Mutability): bool :=
    match m with
    | mutable => true
    | exclusive => true
    | _ => false
    end.

Record Field := {
    is_ref: bool;
}.

(*
 * Classes and type parameters are referenced by an id, which is their identity: two references mean
 * the same declaration exactly when their ids are equal, like the identity comparison in Kotlin.
 * Distinct declarations get distinct ids, even where their names are the same (the T of
 * `class A<T>` and the T of `fun foo<T>`). There are deliberately no names: they are only needed for
 * error messages, and they'd invite mistaking one declaration for another. nat makes a fresh id
 * easy to come by: one more than the largest in use.
 *)
Definition ClassId := nat.
Definition TypeParameterId := nat.

(*
 * BoundBaseType, as it is referenced. What is declared about a class, its supertypes and fields
 * among it, is in its ClassDecl (below). A class can't carry that declaration itself: the
 * supertypes are type references, with type arguments, back into Class.
 *)
Inductive Class :=
    | any
    | some_class (id: ClassId)
    | nothing
    .

Definition Class_eq_dec: forall a b: Class, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(* BoundBaseType.Kind *)
Inductive ClassKind :=
    | class_kind
    | interface_kind
    .

Inductive Variance :=
    | invariant
    | input
    | output
    .

Scheme Equality for Variance.

Definition intersect_variance (a b: Variance): Variance :=
    if Variance_beq a b then a else invariant.

Theorem intersect_variance_comm: forall a b: Variance, intersect_variance a b = intersect_variance b a.
Proof.
    intros [] []; reflexivity.
Qed.

Theorem intersect_variance_assoc: forall a b c: Variance, intersect_variance (intersect_variance a b) c = intersect_variance a (intersect_variance b c).
Proof.
    intros [] [] []; reflexivity.
Qed.

(* EType nests list, for which Rocq would like a scheme that nothing here needs *)
Local Set Warnings "-register-all".

(* BoundTypeReference and its subclasses *)
Inductive EType :=
    (* RootResolvedTypeReference; the mutability is `explicitMutability ?: original?.mutability`.
       The arguments are TypeArguments; no arguments and a null list are the same thing. *)
    | RootResolved (mutability: option Mutability) (class: Class) (arguments: list EType)
    | Nullable (nested: EType)
    | Generic (generic: GenericRef)
    (* ErroneousType; the mutability is `astNode.mutability` *)
    | Error (mutability: option Mutability) (message: string)
    (* BoundTypeArgument *)
    | TypeArgument (variance: Variance) (nested: EType)
    (* a generic type under inference; wraps a GenericTypeReference, just like the Kotlin class *)
    | TypeVariable (generic: GenericRef)
    (* BoundIntersectionTypeReference; its mutability is the intersection of that of the components *)
    | Intersection (components: list EType)
(* GenericTypeReference; the mutability is `original.mutability`. The effective bound is the bound
   of the parameter, with the mutability and nullability of this reference applied. *)
with GenericRef :=
    | mkGenericRef (mutability: option Mutability) (param: TypeParameterId) (effective_bound: EType)
.

(* The declaration of a type parameter (BoundTypeParameter), the counterpart to a GenericRef. *)
Record TypeParameterDecl := {
    param_id: TypeParameterId;
    bound: EType;
}.

(* The declaration of a class (BoundBaseType), the counterpart to a Class reference. *)
Record ClassDecl := {
    kind: ClassKind;
    (* BoundBaseType.isCoreScalar: the numeric types and bool, whose references are always immutable *)
    is_core_scalar: bool;
    type_parameters: list TypeParameterDecl;
    (* RootResolved references to the direct supertypes, their arguments in terms of type_parameters *)
    supertypes: list EType;
    fields: list Field;
}.

End Model.
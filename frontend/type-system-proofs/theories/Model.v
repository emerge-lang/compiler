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

CoInductive Class :=
    | newClass (superclasses: list Class) (fields: list Field)
    .

Record EType := {
    nullable: bool,
    mutability: Mutability;
    class: Class;
}.

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


(*
 * A translation of BoundTypeReference.unify, and of the "is subtype of" relation built on it, from
 * ../src/main/kotlin/compiler/binding/type.
 *
 * `target.unify(assignee, location, carry)` asserts that a value of type `assignee` can be assigned to
 * a reference of type `target`. It never fails outright: it returns `carry`, extended with bindings
 * for the type variables under inference and with a diagnostic for every reason the assignment
 * doesn't hold. `a isAssignableTo b` is then just "unifying `b` with `a` produces no errors".
 *
 * Where this model deviates from the Kotlin code:
 *
 * - No diagnostics, just whether the unification failed. Once it has, unify stops, where Kotlin
 *   carries on to collect more diagnostics; and where Kotlin does extra work only to pick the more
 *   helpful diagnostic, this doesn't. TypeUnification.fromExplicit, the explicit type arguments
 *   of an invocation, is left out; plus_exact_binding serves the capture of type arguments.
 * - Everything that unify only consumes, rather than decides, is a section variable, the
 *   Environment: the class declarations, what is derived from them (the transitive supertypes,
 *   their type arguments), and the lattice operations the inference uses
 *   (closestCommonSupertypeWith, intersect). They are translations of their own.
 * - Termination. unify recurses into types it builds on the way (the instantiated supertype of
 *   the assignee, the bounds of type variables, `Any` standing in for a covered intersection
 *   component), so it isn't structurally recursive. It takes fuel, and gives no answer (None) when
 *   that runs out, so that neither a success nor a failure is ever down to a lack of fuel.
 * - Exceptions. Where the Kotlin code throws (TypeVariableNotUnderInferenceException, the
 *   InternalCompilerError for unifying two type variables), unify gives no answer either.
 *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From EmergeTypeSystem Require Import Model.

Section Subtyping.

Definition class_eqb (a b: Class): bool := if Class_eq_dec a b then true else false.
Definition param_eqb (a b: TypeParameterId): bool := Nat.eqb a b.

Variable env: Environment.

(* BoundBaseType.Kind.allowsSubtypes *)
Definition allows_subtypes (c: Class): bool :=
    match kind (declaration_of env c) with
    | class_kind => false
    | interface_kind => true
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* Properties of types that unify reads                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* BoundBaseType.isSubtypeOf *)
Definition base_type_is_subtype_of (sub super: Class): bool :=
    if class_eqb super sub then true else
    if class_eqb super any then true else
    if class_eqb super nothing then false else
    if class_eqb sub nothing then true else
    existsb (class_eqb super) (supertypes_of env sub).

(* the default mutability of a reference, `mutability ?: READONLY` *)
Definition or_readonly (m: option Mutability): Mutability :=
    match m with Some m => m | None => readonly end.

(* RootResolvedTypeReference.hasSameBaseTypeAs *)
Fixpoint has_base_type (c: Class) (other: EType): bool :=
    match other with
    | RootResolved _ c' _ => class_eqb c c'
    | Nullable n => has_base_type c n
    | TypeArgument _ _ n => has_base_type c n
    | _ => false
    end.

(* GenericTypeReference.hasSameBaseTypeAs *)
Fixpoint is_generic_of (p: TypeParameterId) (other: EType): bool :=
    match other with
    | Generic (mkGenericRef _ _ p' _) => param_eqb p p'
    | Nullable n => is_generic_of p n
    | _ => false
    end.

(* BoundTypeReference.hasSameBaseTypeAs *)
Fixpoint has_same_base_type_as (t other: EType): bool :=
    match t with
    | RootResolved _ c _ => has_base_type c other
    | Nullable n => has_same_base_type_as n other
    | Generic (mkGenericRef _ _ p _) => is_generic_of p other
    | Error _ _ => true
    | TypeArgument _ _ n => has_same_base_type_as n other
    (* Kotlin compares for equality; comparing the parameters is close enough for base types *)
    | TypeVariable (mkGenericRef _ _ p _) =>
        match other with TypeVariable (mkGenericRef _ _ p' _) => param_eqb p p' | _ => false end
    | Intersection components => existsb (fun c => has_same_base_type_as c other) components
    end.

(* whether `f` holds for any two distinct elements of `l`, like twoElementPermutationsUnordered().any(f) *)
Fixpoint exists_unordered_pair {A: Type} (f: A -> A -> bool) (l: list A): bool :=
    match l with
    | [] => false
    | x :: rest => existsb (f x) rest || exists_unordered_pair f rest
    end.

Definition is_type_variable (t: EType): bool :=
    match t with TypeVariable _ => true | _ => false end.

(* swCtx.getTopType: read Any? *)
Definition top_type: EType := Nullable (RootResolved (Some readonly) any []).

(* swCtx.getBottomType: exclusive Nothing *)
Definition bottom_type: EType := RootResolved (Some exclusive) nothing [].

(* ErroneousType.asAny and ErroneousType.asNothing *)
Definition as_any (m: Mutability): EType := RootResolved (Some m) any [].
Definition as_nothing (m: Mutability): EType := RootResolved (Some m) nothing [].

(* NullableTypeReference.rewrap: nullable, without nesting nullability *)
Definition rewrap_nullable (t: EType): EType :=
    match t with
    | Nullable _ => t
    | _ => Nullable t
    end.

(* BoundTypeReference.withTypeVariables: the references to the type parameters vs become type
   variables, and all references have their bounds with those type variables *)
Fixpoint with_type_variables_in (vs: list TypeParameterId) (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map (with_type_variables_in vs) arguments)
    | Nullable n => Nullable (with_type_variables_in vs n)
    | Generic (mkGenericRef gm nn p ws) =>
        if existsb (param_eqb p) vs
        then TypeVariable (mkGenericRef gm nn p (ws ++ vs))
        else Generic (mkGenericRef gm nn p (ws ++ vs))
    | TypeVariable (mkGenericRef gm nn p ws) => TypeVariable (mkGenericRef gm nn p (ws ++ vs))
    | Error _ _ => t
    | TypeArgument v o n => TypeArgument v o (with_type_variables_in vs n)
    | Intersection components => Intersection (map (with_type_variables_in vs) components)
    end.

Definition with_type_variables (vs: list TypeParameterId) (t: EType): EType :=
    match vs with [] => t | _ => with_type_variables_in vs t end.

(* ---------------------------------------------------------------------------------------------- *)
(* Looking through references to type parameters                                                  *)
(*                                                                                                *)
(* A reference to a type parameter has the properties of its effective bound, which is made from   *)
(* the bound of the parameter (Environment.parameter_bound), not a part of the reference. So the   *)
(* functions that look through a reference aren't structurally recursive. A bound mentions only    *)
(* type parameters declared before (bounds_ranked), so they recurse on the rank of the parameter:  *)
(* each is written once, taking what it gives for a reference from Handlers, and level k gives    *)
(* that for the parameters of rank below k, from level k - 1. For an environment whose bounds      *)
(* aren't ranked, they still give some answer; the facts about them assume bounds_ranked.          *)
(* ---------------------------------------------------------------------------------------------- *)

(* What the functions below give for a reference to a type parameter (Generic or TypeVariable) *)
Record Handlers := mkHandlers {
    h_top_const: GenericRef -> bool;
    h_mutability: GenericRef -> Mutability;
    h_assignment_mutability: GenericRef -> Mutability;
    h_nullable: GenericRef -> bool;
    h_base_type: GenericRef -> Class;
    h_non_nullable_nothing: GenericRef -> bool;
}.

Section WithHandlers.

Variable H: Handlers.

Fixpoint top_const_h (t: EType): bool :=
    match t with
    | RootResolved _ c _ => is_const (declaration_of env c)
    | Nullable n | TypeArgument _ _ n => top_const_h n
    | Generic g | TypeVariable g => h_top_const H g
    | Error _ _ => false
    | Intersection cs => existsb top_const_h cs
    end.

Fixpoint mutability_of_h (t: EType): Mutability :=
    match t with
    | RootResolved m c _ => if is_const (declaration_of env c) then immutable else or_readonly m
    | Nullable n => mutability_of_h n
    | Generic g | TypeVariable g => h_mutability H g
    | Error m _ => or_readonly m
    | TypeArgument _ _ n => mutability_of_h n
    | Intersection components =>
        if existsb top_const_h components then immutable
        else fold_left intersect_mutability (map mutability_of_h components) readonly
    end.

Fixpoint assignment_mutability_h (t: EType): Mutability :=
    match t with
    | RootResolved m c _ => if is_const (declaration_of env c) then exclusive else or_readonly m
    | Nullable n => assignment_mutability_h n
    | Generic g | TypeVariable g => h_assignment_mutability H g
    | Error m _ => or_readonly m
    | TypeArgument _ _ n => assignment_mutability_h n
    | Intersection components => fold_left intersect_mutability (map assignment_mutability_h components) readonly
    end.

Fixpoint is_nullable_h (t: EType): bool :=
    match t with
    | RootResolved _ _ _ => false
    | Nullable _ => true
    | Generic g | TypeVariable g => h_nullable H g
    | Error _ _ => false
    | TypeArgument _ _ n => is_nullable_h n
    | Intersection _ => false
    end.

Fixpoint base_type_of_lower_bound_h (t: EType): Class :=
    match t with
    | RootResolved _ c _ => c
    | Nullable n => base_type_of_lower_bound_h n
    | Generic g | TypeVariable g => h_base_type H g
    | Error _ _ => nothing
    | TypeArgument _ _ n => base_type_of_lower_bound_h n
    | Intersection components => closest_common_super_class env (map base_type_of_lower_bound_h components)
    end.

Definition is_effectively_bottom_type_h (components: list EType): bool :=
    exists_unordered_pair
        (fun a b => negb (has_same_base_type_as a b))
        (filter (fun c => negb (allows_subtypes (base_type_of_lower_bound_h c))) components).

Fixpoint is_non_nullable_nothing_h (t: EType): bool :=
    match t with
    | RootResolved _ c _ => class_eqb c nothing
    | Nullable _ => false
    | Generic g | TypeVariable g => h_non_nullable_nothing H g
    | Error _ _ => false
    | TypeArgument _ _ n => is_non_nullable_nothing_h n
    | Intersection components =>
        existsb is_non_nullable_nothing_h components || is_effectively_bottom_type_h components
    end.

Fixpoint without_null_h (t: EType): EType :=
    match t with
    | Nullable n => without_null_h n
    | Generic (mkGenericRef gm nn p vs) => Generic (mkGenericRef gm (nn || h_nullable H (mkGenericRef gm nn p vs)) p vs)
    | TypeArgument v o n => TypeArgument v o (without_null_h n)
    | _ => t
    end.

Fixpoint with_mutability_h (m: Mutability) (t: EType): EType :=
    match t with
    | RootResolved _ c arguments =>
        RootResolved (Some (if is_const (declaration_of env c) then immutable else m)) c arguments
    | Nullable n => rewrap_nullable (with_mutability_h m n)
    | Generic (mkGenericRef _ nn p vs) => Generic (mkGenericRef (Some m) nn p vs)
    | TypeVariable (mkGenericRef _ nn p vs) => TypeVariable (mkGenericRef (Some m) nn p vs)
    | Error _ _ => t
    | TypeArgument v o n => TypeArgument v o (with_mutability_h m n)
    | Intersection components =>
        let common := fold_left intersect_mutability (map (fun c => assignment_mutability_h (with_mutability_h m c)) components) readonly in
        Intersection (map (with_mutability_h common) components)
    end.

Definition effective_bound_h (g: GenericRef): EType :=
    let declared := parameter_bound env (param_of g) in
    let of_mutability := match given_mutability g with Some m => with_mutability_h m declared | None => declared end in
    let narrowed := if is_narrowed g then without_null_h of_mutability else of_mutability in
    with_type_variables (variables_of g) narrowed.

End WithHandlers.

(* Level k: for the type parameters of rank below k. Below level 0, there are none. *)
Fixpoint level (k: nat): Handlers :=
    match k with
    | 0 => mkHandlers (fun _ => false) (fun _ => readonly) (fun _ => readonly) (fun _ => false) (fun _ => nothing) (fun _ => false)
    | S k' =>
        let L := level k' in
        mkHandlers
            (fun g => top_const_h L (effective_bound_h L g))
            (fun g => mutability_of_h L (effective_bound_h L g))
            (fun g => assignment_mutability_h L (effective_bound_h L g))
            (fun g => is_nullable_h L (effective_bound_h L g))
            (fun g => base_type_of_lower_bound_h L (effective_bound_h L g))
            (fun g => is_non_nullable_nothing_h L (effective_bound_h L g))
    end.

Definition rank_of (g: GenericRef): nat := parameter_rank env (param_of g).

(* GenericTypeReference.effectiveBound: the bound of the parameter, with the given mutability (`m T`),
   without null (`T!`), and with the type variables *)
Definition effective_bound (g: GenericRef): EType := effective_bound_h (level (rank_of g)) g.

(* What a reference to a type parameter has of its effective bound *)
Definition ref_top_const (g: GenericRef): bool := top_const_h (level (rank_of g)) (effective_bound g).
Definition ref_mutability (g: GenericRef): Mutability := mutability_of_h (level (rank_of g)) (effective_bound g).
Definition ref_assignment_mutability (g: GenericRef): Mutability := assignment_mutability_h (level (rank_of g)) (effective_bound g).
Definition ref_nullable (g: GenericRef): bool := is_nullable_h (level (rank_of g)) (effective_bound g).
Definition ref_base_type (g: GenericRef): Class := base_type_of_lower_bound_h (level (rank_of g)) (effective_bound g).
Definition ref_non_nullable_nothing (g: GenericRef): bool := is_non_nullable_nothing_h (level (rank_of g)) (effective_bound g).

Definition top_handlers: Handlers :=
    mkHandlers ref_top_const ref_mutability ref_assignment_mutability ref_nullable ref_base_type ref_non_nullable_nothing.

(* ---------------------------------------------------------------------------------------------- *)
(* Properties of types that unify reads                                                           *)
(* The same as above, with what a reference has of its effective bound                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* Whether the type is a const class, or the values of it are of one: an intersection with such a
   component, a reference to a type parameter bounded by one *)
Fixpoint top_const (t: EType): bool :=
    match t with
    | RootResolved _ c _ => is_const (declaration_of env c)
    | Nullable n | TypeArgument _ _ n => top_const n
    | Generic g | TypeVariable g => ref_top_const g
    | Error _ _ => false
    | Intersection cs => existsb top_const cs
    end.

(* BoundTypeReference.mutability *)
Fixpoint mutability_of (t: EType): Mutability :=
    match t with
    | RootResolved m c _ =>
        if is_const (declaration_of env c) then immutable else or_readonly m
    | Nullable n => mutability_of n
    (* the given mutability is applied to the effective bound, which carries it from there *)
    | Generic g | TypeVariable g => ref_mutability g
    | Error m _ => or_readonly m
    | TypeArgument _ _ n => mutability_of n
    (* readonly is the neutral element of intersect_mutability. Its values are objects of a const
       class where one of the components is one: then it is const *)
    | Intersection components =>
        if existsb top_const components then immutable
        else fold_left intersect_mutability (map mutability_of components) readonly
    end.

(* BoundTypeReference.assignmentMutability: the mutability a value of the type is assigned as. That
   is its own, but exclusive for an object of a const class: nothing can mutate it, so it keeps what a
   reference of any mutability promises, and it fits all of them. Its references stay immutable
   (mutability_of), so that nothing reads or writes them as mutable. *)
Fixpoint assignment_mutability (t: EType): Mutability :=
    match t with
    | RootResolved m c _ =>
        if is_const (declaration_of env c) then exclusive else or_readonly m
    | Nullable n => assignment_mutability n
    | Generic g | TypeVariable g => ref_assignment_mutability g
    | Error m _ => or_readonly m
    | TypeArgument _ _ n => assignment_mutability n
    | Intersection components => fold_left intersect_mutability (map assignment_mutability components) readonly
    end.

(* BoundTypeReference.isNullable *)
Fixpoint is_nullable (t: EType): bool :=
    match t with
    | RootResolved _ _ _ => false
    | Nullable _ => true
    | Generic g | TypeVariable g => ref_nullable g
    | Error _ _ => false
    | TypeArgument _ _ n => is_nullable n
    | Intersection _ => false
    end.

(* BoundTypeReference.baseTypeOfLowerBound *)
Fixpoint base_type_of_lower_bound (t: EType): Class :=
    match t with
    | RootResolved _ c _ => c
    | Nullable n => base_type_of_lower_bound n
    | Generic g | TypeVariable g => ref_base_type g
    | Error _ _ => nothing
    | TypeArgument _ _ n => base_type_of_lower_bound n
    | Intersection components => closest_common_super_class env (map base_type_of_lower_bound components)
    end.

(* BoundIntersectionTypeReference.simplifyIsEffectivelyBottomType: two unrelated classes have no
   common subtype *)
Definition is_effectively_bottom_type (components: list EType): bool :=
    exists_unordered_pair
        (fun a b => negb (has_same_base_type_as a b))
        (filter (fun c => negb (allows_subtypes (base_type_of_lower_bound c))) components).

(* BoundTypeReference.isNonNullableNothing *)
Fixpoint is_non_nullable_nothing (t: EType): bool :=
    match t with
    | RootResolved _ c _ => class_eqb c nothing
    | Nullable _ => false
    | Generic g | TypeVariable g => ref_non_nullable_nothing g
    | Error _ _ => false
    | TypeArgument _ _ n => is_non_nullable_nothing n
    | Intersection components =>
        existsb is_non_nullable_nothing components || is_effectively_bottom_type components
    end.

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating type parameters                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* BoundTypeReference.withCombinedNullability(NOT_NULLABLE): `V!` for a type parameter V, which
   narrows the reference where the bound is nullable *)
Fixpoint without_null (t: EType): EType :=
    match t with
    | Nullable n => without_null n
    | Generic (mkGenericRef gm nn p vs) => Generic (mkGenericRef gm (nn || ref_nullable (mkGenericRef gm nn p vs)) p vs)
    | TypeArgument v o n => TypeArgument v o (without_null n)
    | _ => t
    end.

(* BoundTypeReference.withMutability. An intersection (BoundIntersectionTypeReference.mapComponents)
   gives its components the mutability they are assigned as in common once they took the given one:
   exclusive, where one of them is a const class, as in of_components. Kotlin applies that to the
   components it applied the given mutability to; applying a mutability replaces the one before.
   A reference to a type parameter takes it as its given mutability, which applies to its bound. *)
Fixpoint with_mutability (m: Mutability) (t: EType): EType :=
    match t with
    | RootResolved _ c arguments =>
        RootResolved (Some (if is_const (declaration_of env c) then immutable else m)) c arguments
    | Nullable n => rewrap_nullable (with_mutability m n)
    | Generic (mkGenericRef _ nn p vs) => Generic (mkGenericRef (Some m) nn p vs)
    | TypeVariable (mkGenericRef _ nn p vs) => TypeVariable (mkGenericRef (Some m) nn p vs)
    | Error _ _ => t
    | TypeArgument v o n => TypeArgument v o (with_mutability m n)
    | Intersection components =>
        let common := fold_left intersect_mutability (map (fun c => assignment_mutability (with_mutability m c)) components) readonly in
        Intersection (map (with_mutability common) components)
    end.

(* What the type parameters are bound to: the type arguments of a reference, a TypeUnification's
   inherent type bindings *)
Definition Bindings := list (TypeParameterId * EType).

Fixpoint lookup_binding (bindings: Bindings) (p: TypeParameterId): option EType :=
    match bindings with
    | [] => None
    | (p', argument) :: rest => if param_eqb p p' then Some argument else lookup_binding rest p
    end.

(* The ownership of a type parameter becomes that of the type argument it is bound to. A type
   parameter without a binding is replaced by its bound, whose ownership is unknown: any. *)
Definition instantiate_ownership (bindings: Bindings) (o: Ownership): Ownership :=
    match o with
    | parameter_ownership p =>
        match lookup_binding bindings p with
        | Some (TypeArgument _ argument_ownership _) => argument_ownership
        | _ => any_ownership
        end
    | owned | ref | any_ownership => o
    end.

(* A type argument that stands for more than one type argument: one of a variance, `out X` for X and
   all its subtypes, or of any ownership, `any X` for `owned X` and `ref X`. Kotlin has no ownership,
   yet, so there it's just the variance. *)
Definition is_loose (a: EType): bool :=
    match a with
    | TypeArgument v o _ => negb (Variance_beq v invariant) || match o with any_ownership => true | _ => false end
    | _ => false
    end.

(* Whether the type mentions a type parameter that is bound to a loose type argument *)
Fixpoint mentions_loosely_bound (bindings: Bindings) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => existsb (mentions_loosely_bound bindings) arguments
    | Nullable n => mentions_loosely_bound bindings n
    | Generic (mkGenericRef _ _ p _)
    | TypeVariable (mkGenericRef _ _ p _) =>
        match lookup_binding bindings p with
        | Some argument => is_loose argument
        | None => false
        end
    | Error _ _ => false
    | TypeArgument _ _ n => mentions_loosely_bound bindings n
    | Intersection components => existsb (mentions_loosely_bound bindings) components
    end.

(* The same, in the type arguments of the type, rather than as the type itself *)
Fixpoint mentions_loosely_bound_in_arguments (bindings: Bindings) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => existsb (mentions_loosely_bound bindings) arguments
    | Nullable n => mentions_loosely_bound_in_arguments bindings n
    | Intersection components => existsb (mentions_loosely_bound_in_arguments bindings) components
    | _ => false
    end.

Definition nests_argument (t: EType): bool :=
    match t with
    | TypeArgument _ _ _ | Nullable (TypeArgument _ _ _) => true
    | _ => false
    end.

(* TypeUnification.getFinalTypeFor: a type parameter bound exactly is the type it is bound to. That
   is no type argument (BoundTypeArgument checks); where it would be, the type argument stays *)
Definition final_argument (argument: EType): EType :=
    match argument with
    | TypeArgument _ _ x => if is_loose argument || nests_argument x then argument else x
    | _ => argument
    end.

(* BoundIntersectionTypeReference.intersectedComponents: the components of the intersection a type is,
   each nullable iff the type is; the type alone otherwise *)
Definition intersected_components (t: EType): list EType :=
    match t with
    | Intersection components => components
    | Nullable (Intersection components) => map Nullable components
    | _ => [t]
    end.

(* BoundIntersectionTypeReference.ofComponents, without simplifying: the components non-null, of
   their common mutability; nullable iff all of them are. That is the mutability they are assigned as
   in common: exclusive, where one of them is a const class, as the values are its objects. *)
Definition of_components (components: list EType): EType :=
    match components with
    | [component] => component
    | _ =>
        let m := fold_left intersect_mutability (map assignment_mutability components) readonly in
        let non_nullable := Intersection (map (fun c => with_mutability m (without_null c)) components) in
        if forallb is_nullable components then Nullable non_nullable else non_nullable
    end.

(* instantiate, taking what a reference to a type parameter without a binding becomes from unbound *)
Section InstantiateWith.

Variable unbound: GenericRef -> EType.

Fixpoint instantiate_h (bindings: Bindings) (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map (instantiate_h bindings) arguments)
    | Nullable n => rewrap_nullable (instantiate_h bindings n)
    | Generic ((mkGenericRef given narrowed p _) as g) =>
        let final_value :=
            match lookup_binding bindings p with
            | Some argument => final_argument argument
            | None => unbound g
            end in
        let of_mutability :=
            match given with
            | Some m => with_mutability (intersect_mutability (mutability_of final_value) m) final_value
            | None => final_value
            end in
        if narrowed then without_null of_mutability else of_mutability
    | Error _ _ => t
    | TypeArgument v o n =>
        let o' := instantiate_ownership bindings o in
        let n_instantiated := instantiate_h bindings n in
        let is_nullable_instantiated := match n_instantiated with Nullable _ => true | _ => false end in
        let n_non_null := match n_instantiated with Nullable x => x | _ => n_instantiated end in
        match n_non_null with
        | TypeArgument nested_variance _ nested_type =>
            if Variance_beq nested_variance invariant || Variance_beq v invariant || Variance_beq nested_variance v then
                let merged_variance := if Variance_beq nested_variance invariant then v else nested_variance in
                TypeArgument merged_variance o'
                    (if is_nullable_instantiated then rewrap_nullable nested_type else nested_type)
            else
                match v with
                | output => TypeArgument output o' top_type
                | _ => TypeArgument input o' bottom_type
                end
        | _ =>
            if mentions_loosely_bound_in_arguments bindings n then
                match v with
                | input => TypeArgument input o' bottom_type
                | invariant | output => TypeArgument output o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
                end
            else TypeArgument v o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
        end
    | TypeVariable ((mkGenericRef _ _ p _) as g) =>
        match lookup_binding bindings p with
        | Some argument => final_argument argument
        | None => unbound g
        end
    | Intersection components => of_components (flat_map intersected_components (map (instantiate_h bindings) components))
    end.

End InstantiateWith.

(* A function that looks through references to type parameters, f_h taking what it gives for
   them: at level k, for the type parameters of rank below k (see Handlers), what it gives for the
   effective bound. through is that for a reference, from the level of its rank. *)
Section ThroughBounds.

Context {X: Type}.
Variable f_h: (GenericRef -> X) -> EType -> X.
Variable default: X.

Fixpoint through_level (k: nat) (g: GenericRef): X :=
    match k with
    | 0 => default
    | S k' => f_h (through_level k') (effective_bound g)
    end.

Definition through (g: GenericRef): X := through_level (S (rank_of g)) g.

End ThroughBounds.

(* What a reference to a type parameter without a binding becomes: its effective bound, instantiated *)
Definition instantiate_unbound (bindings: Bindings) (g: GenericRef): EType :=
    through (fun unbound => instantiate_h unbound bindings) top_type g.

(*
 * BoundTypeReference.instantiateAllParameters, extended with ownership. Where it deviates:
 * - TypeUnification.getFinalValueFor instantiates the free variables in a binding. The bindings here
 *   are those of a type reference (TypeUnification.forSubstitution), in which type variables belong to
 *   another inference; they stay as they are (TypeVariable.instantiateFreeVariables), so that unifying
 *   with the instantiated type constrains them. They do occur: in `fn f<T>(c: Consumer<in MyLst<T>>)`
 *   called with a `Consumer<in Lst<X>>`, `MyLst<T>` becomes the assignee of `Lst<X>`, with T under
 *   inference. So this is left out.
 * - A type parameter without a binding is replaced by its bound; Kotlin uses the declared bound,
 *   this the effective bound of the reference (instantiate_unbound).
 * - BoundIntersectionTypeReference simplifies the instantiated intersection, this doesn't; nor does
 *   this keep the intersection as it is where no component changed.
 *)
Fixpoint instantiate (bindings: Bindings) (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map (instantiate bindings) arguments)
    | Nullable n => rewrap_nullable (instantiate bindings n)
    | Generic ((mkGenericRef given narrowed p _) as g) =>
        let final_value :=
            match lookup_binding bindings p with
            | Some argument => final_argument argument
            | None => instantiate_unbound bindings g
            end in
        let of_mutability :=
            match given with
            (* a value of type `m T` is a T of a mutability that fits m *)
            | Some m => with_mutability (intersect_mutability (mutability_of final_value) m) final_value
            | None => final_value
            end in
        (* `T!` *)
        if narrowed then without_null of_mutability else of_mutability
    | Error _ _ => t
    (* BoundTypeArgument.instantiateAllParameters. When the nested type becomes a type argument of its
       own (a type parameter replaced by its binding), their variances merge: `out T` with T bound to
       `out X` is `out X`. Of opposite variances, `out T` with T bound to `in X` is known no closer than
       `out read Any?` (as in unify), and `in T` with T bound to `out X` takes nothing: `in Nothing`.
       A type parameter bound to an out- or in-variant type argument deeper down widens the type
       argument: with T bound to `out X`, `Box<Box<T>>` is no `Box<Box<out X>>`, which would take any
       `Box<out X>`, but a `Box<out Box<out X>>`. And `Consumer<in Box<T>>` takes nothing anymore:
       `Consumer<in Nothing>`, which every `Consumer<in Y>` is assignable to (unlike `Consumer<out read
       Any?>`). The same goes for type parameters bound to type arguments of any ownership: with T bound
       to `any X`, `Box<Box<T>>` would take a `Box<ref X>` where there is a `Box<Box<owned X>>`. *)
    | TypeArgument v o n =>
        let o' := instantiate_ownership bindings o in
        let n_instantiated := instantiate bindings n in
        let is_nullable_instantiated := match n_instantiated with Nullable _ => true | _ => false end in
        let n_non_null := match n_instantiated with Nullable x => x | _ => n_instantiated end in
        match n_non_null with
        | TypeArgument nested_variance _ nested_type =>
            if Variance_beq nested_variance invariant || Variance_beq v invariant || Variance_beq nested_variance v then
                let merged_variance := if Variance_beq nested_variance invariant then v else nested_variance in
                TypeArgument merged_variance o'
                    (if is_nullable_instantiated then rewrap_nullable nested_type else nested_type)
            else
                match v with
                | output => TypeArgument output o' top_type
                | _ => TypeArgument input o' bottom_type
                end
        | _ =>
            if mentions_loosely_bound_in_arguments bindings n then
                match v with
                | input => TypeArgument input o' bottom_type
                | invariant | output => TypeArgument output o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
                end
            else TypeArgument v o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
        end
    (* TypeVariable.instantiateAllParameters *)
    | TypeVariable ((mkGenericRef _ _ p _) as g) =>
        match lookup_binding bindings p with
        | Some argument => final_argument argument
        | None => instantiate_unbound bindings g
        end
    | Intersection components => of_components (flat_map intersected_components (map (instantiate bindings) components))
    end.

(* RootResolvedTypeReference.inherentTypeBindings: each type parameter of the class is bound to the
   type argument in its place *)
Definition bindings_of (c: Class) (arguments: list EType): Bindings :=
    combine (map param_id (type_parameters (declaration_of env c))) arguments.

(*
 * RootResolvedTypeReference.getInstantiatedSupertype: given a class `sub` with type arguments
 * `arguments` and one of its supertypes `super` (never `sub` itself, nor `nothing`), the type
 * arguments `super` has as a supertype of that reference.
 *)
Definition parameterized_supertype_arguments (sub: Class) (arguments: list EType) (super: Class): list EType :=
    match parameterized_supertype env sub super with
    | RootResolved _ _ super_arguments => map (instantiate (bindings_of sub arguments)) super_arguments
    | _ => []
    end.


(* ---------------------------------------------------------------------------------------------- *)
(* TypeUnification                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* TypeUnification.VariableState *)
Record VariableState := mkVariableState {
    static_upper_bound: EType;
    upper_bound: EType;
    lower_bound: EType;
    is_exact: bool;
    (* see TypeUnification.plusCapture *)
    is_capturable: bool;
}.

Definition VariableStates := list (TypeParameterId * VariableState).

(*
 * TypeUnification. Its diagnostics are reduced to whether there are any: all the diagnostics unify
 * produces are errors, and what matters here is whether an assignment holds, not why it doesn't.
 * The variable states of a failed unification don't matter either, so there are none.
 *)
Inductive Unification :=
    | Ongoing (variable_states: VariableStates)
    | Failed
    .

(* TypeUnification.EMPTY *)
Definition empty_unification: Unification := Ongoing [].

(* TypeUnification.forInferenceOf; the bounds are expected with their type variables already in
   place (`it.bound.withTypeVariables(parameters)`) *)
Definition for_inference_of (parameters: list (TypeParameterId * EType)) (capturable: list TypeParameterId): Unification :=
    Ongoing (map (fun '(p, bound) => (p, mkVariableState bound bound bottom_type false (existsb (param_eqb p) capturable))) parameters).

Fixpoint lookup_state (states: VariableStates) (p: TypeParameterId): option VariableState :=
    match states with
    | [] => None
    | (p', s) :: rest => if param_eqb p p' then Some s else lookup_state rest p
    end.

(* `states + mapOf(p to s)` *)
Definition set_state (states: VariableStates) (p: TypeParameterId) (s: VariableState): VariableStates :=
    (p, s) :: filter (fun '(p', _) => negb (param_eqb p p')) states.

(*
 * unify gives no answer (None) when it runs out of fuel, and where the Kotlin code throws. Whatever
 * builds on something without an answer has none either, so a failure is never down to fuel.
 *)
Local Notation "'let*' x ':=' e 'in' body" :=
    (match e with Some x => body | None => None end)
    (at level 200, x ident, e at level 100, body at level 200).

(* The shape of BoundTypeReference.unify: `unify target assignee carry` is
   `target.unify(assignee, location, carry)`. *)
Definition UnifyFn := EType -> EType -> Unification -> option Unification.

(*
 * The functions below take the variable states of a unification that hasn't failed (see unify), so
 * any failure of a result is a new one: a Failed result stands for Kotlin's
 * `result.getErrorsNotIn(carry).any()`.
 *)

(* TypeUnification.plusSubtypeConstraint: parameter must be assignable to upper *)
Definition plus_subtype_constraint (unify: UnifyFn) (states: VariableStates) (parameter: TypeParameterId) (upper: EType): option Unification :=
    match lookup_state states parameter with
    (* TypeVariableNotUnderInferenceException *)
    | None => None
    | Some state =>
        if is_exact state then unify upper (upper_bound state) (Ongoing states) else
        let new_upper_bound := intersect env (upper_bound state) upper in
        (* Incompatible constraints. Kotlin also unifies with the static upper bound here, to tell
           whether that or another constraint is to blame; it fails either way. *)
        if is_non_nullable_nothing new_upper_bound then Some Failed else
        let* with_lower_bound := unify new_upper_bound (lower_bound state) (Ongoing states) in
        match with_lower_bound with
        | Failed => Some Failed
        | Ongoing new_states => Some (Ongoing (set_state new_states parameter
            (mkVariableState (static_upper_bound state) new_upper_bound (lower_bound state) false (is_capturable state))))
        end
    end.

(* TypeUnification.plusSupertypeConstraint: lower must be assignable to parameter *)
Definition plus_supertype_constraint (unify: UnifyFn) (states: VariableStates) (parameter: TypeParameterId) (lower: EType): option Unification :=
    match lookup_state states parameter with
    (* TypeVariableNotUnderInferenceException *)
    | None => None
    | Some state =>
        if is_exact state then unify (lower_bound state) lower (Ongoing states) else
        let new_lower_bound := closest_common_supertype_with env (lower_bound state) lower in
        let* with_upper_bound := unify (upper_bound state) new_lower_bound (Ongoing states) in
        match with_upper_bound with
        (* Incompatible constraints. Kotlin also unifies with the static upper bound here, to tell
           whether that or another constraint is to blame; it fails either way. *)
        | Failed => Some Failed
        | Ongoing new_states => Some (Ongoing (set_state new_states parameter
            (mkVariableState (static_upper_bound state) (upper_bound state) new_lower_bound false (is_capturable state))))
        end
    end.

(* TypeUnification.plusExactBinding: parameter is exactly the type argument binding, whose type must
   be within the bounds so far *)
Definition plus_exact_binding (unify: UnifyFn) (states: VariableStates) (parameter: TypeParameterId) (binding: EType): option Unification :=
    match lookup_state states parameter with
    (* TypeVariableNotUnderInferenceException *)
    | None => None
    | Some state =>
        let binding_type := match binding with TypeArgument _ _ t => t | _ => binding end in
        let* with_upper_bound := unify (upper_bound state) binding_type (Ongoing states) in
        match with_upper_bound with
        | Failed => Some Failed
        | Ongoing _ =>
            let* with_lower_bound := unify binding (lower_bound state) (Ongoing states) in
            match with_lower_bound with
            | Failed => Some Failed
            | Ongoing new_states => Some (Ongoing (set_state new_states parameter
                (mkVariableState (static_upper_bound state) binding binding true (is_capturable state))))
            end
        end
    end.

(* TypeUnification.plusCapture: a type variable that may be captured (one of the type parameters of the
   class of a receiver), and isn't bound exactly yet, in place of the type of an invariant type
   argument. It is bound exactly to the type argument assigned (plus_exact_binding); one of a
   variance stands for all the types it does. *)
Definition capturable (t: EType) (states: VariableStates): option TypeParameterId :=
    match t with
    | TypeVariable (mkGenericRef _ _ p _) =>
        match lookup_state states p with
        | Some state => if is_capturable state && negb (is_exact state) then Some p else None
        | None => None
        end
    | _ => None
    end.

(* TypeVariable.flippedUnify: the variable is the assignee *)
Definition type_variable_flipped_unify (unify: UnifyFn) (target: EType) (parameter: TypeParameterId) (states: VariableStates): option Unification :=
    plus_subtype_constraint unify states parameter target.

(* The first of the candidates for which attempt doesn't fail, and the variable states the attempt
   ends with; Some None if there is none. Like Kotlin's firstOrNull on a sequence, it stops there. *)
Fixpoint find_first (attempt: EType -> option Unification) (candidates: list EType): option (option (EType * VariableStates)) :=
    match candidates with
    | [] => Some None
    | candidate :: rest =>
        let* result := attempt candidate in
        match result with
        | Failed => find_first attempt rest
        | Ongoing states => Some (Some (candidate, states))
        end
    end.

(* BoundIntersectionTypeReference.flippedUnify: the intersection is the assignee; the first
   component that is assignable to target wins *)
Definition intersection_flipped_unify (unify: UnifyFn) (target: EType) (components: list EType) (states: VariableStates): option Unification :=
    let* first := find_first (fun component => unify target component (Ongoing states)) components in
    match first with
    | Some (_, success) => Some (Ongoing success)
    | None => Some Failed
    end.

(* fold_left, for a function that may not give an answer *)
Fixpoint fold_unify {A: Type} (f: Unification -> A -> option Unification) (l: list A) (carry: Unification): option Unification :=
    match l with
    | [] => Some carry
    | x :: rest => let* next := f carry x in fold_unify f rest next
    end.

Definition unify_arguments (unify: UnifyFn) (targets assignees: list EType) (states: VariableStates): option Unification :=
    fold_unify (fun inner '(target, assignee) => unify target assignee inner) (combine targets assignees) (Ongoing states).

(* ---------------------------------------------------------------------------------------------- *)
(* The unify implementations of the subclasses of BoundTypeReference                              *)
(* `unify` is the recursive call; `self` is the target                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* What a value of a type argument can be read as: an in-variant one is known no closer than
   `read Any?` *)
Definition read_type (v: Variance) (type: EType): EType :=
    match v with input => top_type | _ => type end.

(* RootResolvedTypeReference.unify *)
Definition unify_root_resolved (unify: UnifyFn) (self: EType) (base_type: Class) (arguments: list EType) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | RootResolved _ assignee_base_type assignee_arguments =>
        if negb (base_type_is_subtype_of assignee_base_type base_type) then Some Failed else
        if negb (Model.is_subtype_of (assignment_mutability assignee) (assignment_mutability self)) then Some Failed else
        (* Nothing is a subtype of every other possible type, which cannot be denoted in source code *)
        if class_eqb assignee_base_type nothing then Some (Ongoing states) else
        let normalized_assignee_arguments :=
            if class_eqb assignee_base_type base_type
            then assignee_arguments
            else parameterized_supertype_arguments assignee_base_type assignee_arguments base_type in
        unify_arguments unify arguments normalized_assignee_arguments states
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | Generic g => unify self (effective_bound g) (Ongoing states)
    | TypeArgument v _ type => unify self (read_type v type) (Ongoing states)
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    (* a possibly null value to a non-null reference *)
    | Nullable _ => Some Failed
    | Intersection components => intersection_flipped_unify unify self components states
    end.

(* NullableTypeReference.unify *)
Definition unify_nullable (unify: UnifyFn) (self nested assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | Nullable assignee_nested => unify nested assignee_nested (Ongoing states)
    | TypeArgument v _ type => unify self (read_type v type) (Ongoing states)
    (* null is taken care of: what's left is whether `V!` is a subtype of nested *)
    | Generic _ => unify nested (without_null assignee) (Ongoing states)
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    | _ => unify nested assignee (Ongoing states)
    end.

(* GenericTypeReference.unify *)
Definition unify_generic (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    (* a possibly null value to a non-nullable reference *)
    | Nullable _ => Some Failed
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    (* Nothing, of a mutability that fits *)
    | RootResolved _ _ _ =>
        if is_non_nullable_nothing assignee && Model.is_subtype_of (assignment_mutability assignee) (assignment_mutability self)
        then Some (Ongoing states) else Some Failed
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    | TypeArgument variance _ type => unify self (read_type variance type) (Ongoing states)
    (* the same type parameter, of a mutability and nullability that fit; another one by its bound *)
    | Generic ((mkGenericRef _ _ q _) as g) =>
        if param_eqb q parameter
        then if Model.is_subtype_of (assignment_mutability assignee) (assignment_mutability self) && (negb (is_nullable assignee) || is_nullable self)
             then Some (Ongoing states) else Some Failed
        else unify self (effective_bound g) (Ongoing states)
    | Intersection components => intersection_flipped_unify unify self components states
    end.

(* ErroneousType.unify: acts like Any *)
Definition unify_erroneous (unify: UnifyFn) (self: EType) (m: Mutability) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    | _ => unify (as_any m) assignee (Ongoing states)
    end.

(* Whether a type argument with ownership `sub` can stand in for one with ownership `super`: one with
   any ownership takes all of them; the others only themselves. In particular, a type parameter's
   ownership might be either owned or ref, so neither can stand in for it. *)
Definition ownership_is_assignable_to (sub super: Ownership): bool :=
    match super, sub with
    | any_ownership, _ => true
    | owned, owned | ref, ref => true
    | parameter_ownership p, parameter_ownership p' => param_eqb p p'
    | _, _ => false
    end.

(* BoundTypeArgument.unify *)
Definition unify_type_argument (unify: UnifyFn) (self: EType) (variance: Variance) (ownership: Ownership) (type assignee: EType) (states: VariableStates): option Unification :=
    let assignee_is_type_argument := match assignee with TypeArgument _ _ _ => true | _ => false end in
    (* nothing but Nothing can be assigned to a reference of an out-variant type *)
    if negb assignee_is_type_argument && Variance_beq variance output then
        if is_non_nullable_nothing assignee then Some (Ongoing states) else Some Failed
    else
    match assignee with
    | RootResolved _ _ _
    | Nullable _ => unify type assignee (Ongoing states)
    | TypeArgument assignee_variance assignee_ownership assignee_type =>
        if negb (ownership_is_assignable_to assignee_ownership ownership) then Some Failed else
        match variance, assignee_variance with
        | invariant, _ =>
            match capturable type states with
            | Some p => plus_exact_binding unify states p assignee
            | None =>
                match assignee_variance with
                (* the target uses the type both in IN and OUT fashion, the source must match exactly *)
                | invariant =>
                    let* carry2 := unify type assignee_type (Ongoing states) in
                    unify assignee_type type carry2
                | _ => Some Failed
                end
            end
        | output, output
        | output, invariant => unify type assignee_type (Ongoing states)
        (* What an in-variant type argument gives out is known no closer than `read Any?` *)
        | output, input => unify type top_type (Ongoing states)
        (* IN variance reverses the hierarchy direction *)
        | input, input
        | input, invariant => unify assignee_type type (Ongoing states)
        (* An out-variant type argument takes nothing but Nothing *)
        | input, output => unify bottom_type type (Ongoing states)
        end
    | Generic _ => unify type assignee (Ongoing states)
    | Intersection components => intersection_flipped_unify unify self components states
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    end.

(* TypeVariable.unify *)
(* What a value of the assignee can be read as, mutability-wise *)
Definition assignee_mutability (assignee: EType): Mutability :=
    match assignee with TypeArgument input _ _ => readonly | _ => assignment_mutability assignee end.

(* For `m T`, the variable T takes values of a mutability that fits m, only *)
Definition given_mutability_fits (self assignee: EType): bool :=
    match self with
    | TypeVariable (mkGenericRef (Some m) _ _ _) => Model.is_subtype_of (assignee_mutability assignee) m
    | _ => true
    end.

Definition unify_type_variable (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | RootResolved _ _ _
    | Generic _
    | Intersection _
    | TypeArgument _ _ _ =>
        if given_mutability_fits self assignee then plus_supertype_constraint unify states parameter assignee else Some Failed
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    (* Kotlin throws an InternalCompilerError *)
    | TypeVariable _ => None
    | Nullable nested =>
        if negb (given_mutability_fits self assignee) then Some Failed else
        if is_nullable self then plus_supertype_constraint unify states parameter assignee else
        (* A possibly null value to a non-nullable reference. Kotlin carries on unifying without
           the null, for the sake of more diagnostics; it fails either way. *)
        Some Failed
    end.

(*
 * BoundIntersectionTypeReference.unify. Types are seen as the promises a value makes to its users:
 * before unifying the type variables among the components, the promises already covered by the
 * other components are subtracted from the assignee, so as not to force the variables into a
 * needlessly narrow corner.
 *)
Definition unify_intersection (unify: UnifyFn) (self: EType) (components: list EType) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | Nullable nested =>
        (* a possibly null value to a non-null reference *)
        if negb (is_nullable self) then Some Failed else unify self nested (Ongoing states)
    | TypeVariable (mkGenericRef _ _ p _) => type_variable_flipped_unify unify self p states
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | _ =>
        let var_components := filter is_type_variable components in
        let non_var_components := filter (fun c => negb (is_type_variable c)) components in
        let* carry2 := fold_unify (fun inner component => unify component assignee inner) non_var_components (Ongoing states) in
        match carry2 with
        | Failed => Some Failed
        | Ongoing states2 =>
            let* covering := find_first (fun component => unify component assignee (Ongoing states2)) non_var_components in
            let '(new_assignee, states3) :=
                match covering with
                | None => (assignee, states2)
                | Some (covering, states3) =>
                    let covered_any := RootResolved
                        (Some (intersect_mutability (mutability_of assignee) (mutability_of covering)))
                        any [] in
                    let new_assignee :=
                        if negb (is_nullable covering) && is_nullable assignee
                        then Nullable covered_any
                        else covered_any in
                    (new_assignee, states3)
                end in
            (* where a variable takes no Any, as it may be bound to something narrower already, it
               takes the assignee itself *)
            fold_unify (fun inner component =>
                match unify component new_assignee inner with
                | Some Failed => unify component assignee inner
                | r => r
                end) var_components (Ongoing states3)
        end
    end.

(* BoundTypeReference.unify, dispatching on the class of the target *)
Definition unify_step (unify: UnifyFn) (target assignee: EType) (states: VariableStates): option Unification :=
    match target with
    | RootResolved _ base_type arguments => unify_root_resolved unify target base_type arguments assignee states
    | Nullable nested => unify_nullable unify target nested assignee states
    | Generic (mkGenericRef _ _ parameter _) => unify_generic unify target parameter assignee states
    | Error m _ => unify_erroneous unify target (or_readonly m) assignee states
    | TypeArgument variance ownership type => unify_type_argument unify target variance ownership type assignee states
    | TypeVariable (mkGenericRef _ _ parameter _) => unify_type_variable unify target parameter assignee states
    | Intersection components => unify_intersection unify target components assignee states
    end.

(*
 * Once a unification has failed, it stays failed; nothing that follows changes the outcome. So
 * unify stops there, where Kotlin carries on collecting diagnostics.
 *)
Fixpoint unify (fuel: nat) (target assignee: EType) (carry: Unification): option Unification :=
    match carry with
    | Failed => Some Failed
    | Ongoing states =>
        match fuel with
        | O => None
        | S fuel' => unify_step (unify fuel') target assignee states
        end
    end.

(* BoundTypeReference.isAssignableTo: whether a value of type `sub` can be assigned to a reference
   of type `super`, i.e. whether `sub` is a subtype of `super`. None if unify gives no answer. *)
Definition is_assignable_to (fuel: nat) (sub super: EType): option bool :=
    option_map
        (fun u => match u with Ongoing _ => true | Failed => false end)
        (unify fuel super sub empty_unification).

Lemma unify_keeps_failure: forall fuel target assignee,
    unify fuel target assignee Failed = Some Failed.
Proof. intros [|fuel] target assignee; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* More fuel never changes an answer                                                               *)
(* So an answer unify gives with some fuel is the answer: the one it gives with any more fuel,    *)
(* and hence the one of the unbounded Kotlin implementation.                                      *)
(* ---------------------------------------------------------------------------------------------- *)

(* g gives every answer f gives, and maybe more *)
Definition refines (f g: UnifyFn): Prop :=
    forall target assignee carry u, f target assignee carry = Some u -> g target assignee carry = Some u.

Lemma fold_unify_refines: forall {A: Type} (h k: Unification -> A -> option Unification) l carry u,
    (forall inner x v, h inner x = Some v -> k inner x = Some v) ->
    fold_unify h l carry = Some u -> fold_unify k l carry = Some u.
Proof.
    intros A h k l. induction l as [|x rest IH]; intros carry u Hhk H; simpl in *.
    - exact H.
    - destruct (h carry x) as [next|] eqn:E; [|discriminate].
      rewrite (Hhk _ _ _ E). apply IH; assumption.
Qed.

Lemma find_first_refines: forall (h k: EType -> option Unification) candidates result,
    (forall x v, h x = Some v -> k x = Some v) ->
    find_first h candidates = Some result -> find_first k candidates = Some result.
Proof.
    intros h k candidates. induction candidates as [|x rest IH]; intros result Hhk H; simpl in *.
    - exact H.
    - destruct (h x) as [v|] eqn:E; [|discriminate].
      rewrite (Hhk _ _ E). destruct v; [|apply IH]; assumption.
Qed.

(* The obligation of fold_unify_refines and find_first_refines: the function given to them calls f
   where the other calls g. *)
Ltac solve_pointwise Hfg :=
    intros; cbn beta in *;
    first
        [ apply Hfg; assumption
        | match goal with x: _ * _ |- _ => destruct x end; apply Hfg; assumption
        (* a call of f whose failure falls back on another one *)
        | match goal with Hm: context [match ?h ?t ?a ?c with _ => _ end] |- _ =>
            let E := fresh "E" in
            destruct (h t a c) as [[?|]|] eqn:E; cbn iota in Hm;
            [rewrite (Hfg _ _ _ _ E); exact Hm|rewrite (Hfg _ _ _ _ E); cbn iota; apply Hfg; exact Hm|discriminate Hm]
          end ].

(* Given `H: <expression calling f> = Some u`, shows `<the same expression calling g> = Some u`, by
   following the evaluation of both in lockstep: the goal is the same expression, so every case
   distinction made on H is made on the goal as well. Only ever reduces, never unfolds: unfolding
   the conditions would multiply the case distinctions. *)
Ltac solve_refines Hfg H :=
    match type of Hfg with refines ?f ?g =>
    repeat (cbn beta iota zeta in H |- *;
        match type of H with
        | Some _ = Some _ => injection H as <-
        | None = Some _ => discriminate H
        | f ?t ?a ?c = Some ?u => exact (Hfg _ _ _ _ H)
        | context [f ?t ?a ?c] =>
            let E := fresh "E" in
            destruct (f t a c) eqn:E; [rewrite (Hfg _ _ _ _ E)|]
        | context [fold_unify ?h ?l ?c] =>
            match goal with |- context [fold_unify ?k l c] =>
                let E := fresh "E" in
                destruct (fold_unify h l c) eqn:E;
                [rewrite (fold_unify_refines h k l c _ ltac:(solve_pointwise Hfg) E)|]
            end
        | context [find_first ?h ?l] =>
            match goal with |- context [find_first ?k l] =>
                let E := fresh "E" in
                destruct (find_first h l) eqn:E;
                [rewrite (find_first_refines h k l _ ltac:(solve_pointwise Hfg) E)|]
            end
        | context [if ?b then _ else _] => destruct b
        | context [match ?x with _ => _ end] => destruct x
        end);
    try reflexivity
    end.

Section StepRefines.
    Variables f g: UnifyFn.
    Hypothesis Hfg: refines f g.

    Lemma plus_subtype_constraint_refines: forall states p upper u,
        plus_subtype_constraint f states p upper = Some u -> plus_subtype_constraint g states p upper = Some u.
    Proof. intros * H. unfold plus_subtype_constraint in *. solve_refines Hfg H. Qed.

    Lemma plus_supertype_constraint_refines: forall states p lower u,
        plus_supertype_constraint f states p lower = Some u -> plus_supertype_constraint g states p lower = Some u.
    Proof. intros * H. unfold plus_supertype_constraint in *. solve_refines Hfg H. Qed.

    Lemma plus_exact_binding_refines: forall states p binding u,
        plus_exact_binding f states p binding = Some u -> plus_exact_binding g states p binding = Some u.
    Proof. intros * H. unfold plus_exact_binding in *. solve_refines Hfg H. Qed.

    Lemma intersection_flipped_unify_refines: forall target components states u,
        intersection_flipped_unify f target components states = Some u -> intersection_flipped_unify g target components states = Some u.
    Proof. intros * H. unfold intersection_flipped_unify in *. solve_refines Hfg H. Qed.

    Lemma unify_arguments_refines: forall targets assignees states u,
        unify_arguments f targets assignees states = Some u -> unify_arguments g targets assignees states = Some u.
    Proof. intros * H. unfold unify_arguments in *. solve_refines Hfg H. Qed.

    (* the helpers above, where the lockstep evaluation reaches them *)
    Ltac solve_step H :=
        solve_refines Hfg H;
        match type of H with
        | plus_subtype_constraint f ?s ?p ?t = Some _ => exact (plus_subtype_constraint_refines _ _ _ _ H)
        | plus_supertype_constraint f ?s ?p ?t = Some _ => exact (plus_supertype_constraint_refines _ _ _ _ H)
        | type_variable_flipped_unify f ?t ?p ?s = Some _ => exact (plus_subtype_constraint_refines _ _ _ _ H)
        | intersection_flipped_unify f ?t ?cs ?s = Some _ => exact (intersection_flipped_unify_refines _ _ _ _ H)
        | plus_exact_binding f ?s ?p ?t = Some _ => exact (plus_exact_binding_refines _ _ _ _ H)
        | unify_arguments f ?ts ?xs ?s = Some _ => exact (unify_arguments_refines _ _ _ _ H)
        end.

    Lemma unify_step_refines: forall target assignee states u,
        unify_step f target assignee states = Some u -> unify_step g target assignee states = Some u.
    Proof.
        intros target assignee states u H. unfold unify_step in *.
        destruct target as [| |[]| | |[]|]; cbn beta iota zeta in H |- *.
        - unfold unify_root_resolved in *. solve_step H.
        - unfold unify_nullable in *. solve_step H.
        - unfold unify_generic in *. solve_step H.
        - unfold unify_erroneous in *. solve_step H.
        - unfold unify_type_argument in *. solve_step H.
        - unfold unify_type_variable in *. solve_step H.
        - unfold unify_intersection in *. solve_step H.
    Qed.
End StepRefines.

Lemma unify_refines_with_more_fuel: forall fuel, refines (unify fuel) (unify (S fuel)).
Proof.
    induction fuel as [|fuel IH]; intros target assignee [states|] u H; try exact H.
    - discriminate H.
    - change (unify (S (S fuel)) target assignee (Ongoing states)) with
        (unify_step (unify (S fuel)) target assignee states).
      exact (unify_step_refines _ _ IH _ _ _ _ H).
Qed.

Theorem unify_fuel_monotone: forall fuel more_fuel target assignee carry u,
    fuel <= more_fuel ->
    unify fuel target assignee carry = Some u ->
    unify more_fuel target assignee carry = Some u.
Proof.
    intros fuel more_fuel target assignee carry u Hle. induction Hle as [|more_fuel Hle IH]; intros H.
    - exact H.
    - apply unify_refines_with_more_fuel, IH, H.
Qed.

(* Once is_assignable_to answers, that's the answer for any amount of fuel from there on. *)
Theorem is_assignable_to_fuel_monotone: forall fuel more_fuel sub super answer,
    fuel <= more_fuel ->
    is_assignable_to fuel sub super = Some answer ->
    is_assignable_to more_fuel sub super = Some answer.
Proof.
    intros fuel more_fuel sub super answer Hle H. unfold is_assignable_to in *.
    destruct (unify fuel super sub empty_unification) as [u|] eqn:E; [|discriminate].
    rewrite (unify_fuel_monotone fuel more_fuel _ _ _ u Hle E). exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Sanity checks of the translation                                                                *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma mutability_is_subtype_of_refl: forall m, Model.is_subtype_of m m = true.
Proof. intros []; reflexivity. Qed.

Lemma class_eqb_refl: forall c, class_eqb c c = true.
Proof. intros c. unfold class_eqb. destruct (Class_eq_dec c c); congruence. Qed.

(* A type without type arguments is a subtype of itself. *)
Theorem root_resolved_without_arguments_is_assignable_to_itself: forall fuel m c,
    is_assignable_to (S fuel) (RootResolved m c []) (RootResolved m c []) = Some true.
Proof.
    intros fuel m c. unfold is_assignable_to. simpl.
    unfold base_type_is_subtype_of. rewrite class_eqb_refl, mutability_is_subtype_of_refl. simpl.
    destruct (class_eqb c nothing); reflexivity.
Qed.

(* exclusive Nothing is a subtype of every non-nullable class type. *)
Theorem bottom_type_is_assignable_to_root_resolved: forall fuel m c arguments,
    is_const (declaration_of env nothing) = false ->
    is_assignable_to (S fuel) bottom_type (RootResolved m c arguments) = Some true.
Proof.
    intros fuel m c arguments Hnothing. unfold is_assignable_to, bottom_type. simpl.
    unfold unify_root_resolved, base_type_is_subtype_of.
    rewrite (class_eqb_refl nothing). simpl. rewrite Hnothing. simpl.
    destruct (class_eqb c nothing), (class_eqb c any); reflexivity.
Qed.

(* A possibly null value can't be assigned to a non-nullable class type. *)
Theorem nullable_is_not_assignable_to_root_resolved: forall fuel t m c arguments,
    is_assignable_to (S fuel) (Nullable t) (RootResolved m c arguments) = Some false.
Proof. reflexivity. Qed.

(* With T bound to `out X`, `Box<Box<T>>` is a `Box<out Box<out X>>` *)
Example instantiating_widens_nested_type_arguments: forall box x T vs,
    instantiate [(T, TypeArgument output ref (RootResolved None x []))]
        (RootResolved None box [TypeArgument invariant ref
            (RootResolved None box [TypeArgument invariant (parameter_ownership T) (Generic (mkGenericRef None false T vs))])])
    = RootResolved None box [TypeArgument output ref
        (RootResolved None box [TypeArgument output ref (RootResolved None x [])])].
Proof. intros. simpl. unfold param_eqb. rewrite Nat.eqb_refl. reflexivity. Qed.

(* With T bound to `out X`, `Consumer<in Box<T>>` takes nothing anymore *)
Example instantiating_voids_nested_in_variant_type_arguments: forall consumer box x T vs,
    instantiate [(T, TypeArgument output ref (RootResolved None x []))]
        (RootResolved None consumer [TypeArgument input ref
            (RootResolved None box [TypeArgument invariant (parameter_ownership T) (Generic (mkGenericRef None false T vs))])])
    = RootResolved None consumer [TypeArgument input ref bottom_type].
Proof. intros. simpl. unfold param_eqb. rewrite Nat.eqb_refl. reflexivity. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* Ranked bounds                                                                                   *)
(*                                                                                                *)
(* Kotlin resolves the bound of a type parameter with only the type parameters declared before it  *)
(* in scope (so `<T : Box<U>, U>` doesn't resolve). Ranked that way, the functions that look        *)
(* through references to type parameters give what the effective bound has: the equations below.  *)
(* ---------------------------------------------------------------------------------------------- *)

(* All the references to type parameters in t are to ones of a rank below k *)
Fixpoint ranked_below (k: nat) (t: EType): bool :=
    match t with
    | RootResolved _ _ arguments => forallb (ranked_below k) arguments
    | Nullable n | TypeArgument _ _ n => ranked_below k n
    | Generic g | TypeVariable g => Nat.ltb (rank_of g) k
    | Error _ _ => true
    | Intersection components => forallb (ranked_below k) components
    end.

(* A bound mentions only type parameters declared before *)
Definition bounds_ranked: Prop := forall p, ranked_below (parameter_rank env p) (parameter_bound env p) = true.

Lemma ranked_below_mono: forall k k', k <= k' -> forall t, ranked_below k t = true -> ranked_below k' t = true.
Proof.
    intros k k' Hk. fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try exact H.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Ha Hargs].
      rewrite (IH a Ha), (IHa Hargs). reflexivity.
    - exact (IH n H).
    - apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
    - exact (IH n H).
    - apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

(* Two handlers that give the same for the type parameters of rank below k *)
Definition agree (k: nat) (H1 H2: Handlers): Prop := forall g, rank_of g < k ->
    h_top_const H1 g = h_top_const H2 g /\ h_mutability H1 g = h_mutability H2 g
    /\ h_assignment_mutability H1 g = h_assignment_mutability H2 g /\ h_nullable H1 g = h_nullable H2 g
    /\ h_base_type H1 g = h_base_type H2 g /\ h_non_nullable_nothing H1 g = h_non_nullable_nothing H2 g.

Lemma agree_mono: forall k k' H1 H2, k <= k' -> agree k' H1 H2 -> agree k H1 H2.
Proof. intros k k' H1 H2 Hk Ha g Hg. apply Ha. lia. Qed.

Lemma agree_sym: forall k H1 H2, agree k H1 H2 -> agree k H2 H1.
Proof. intros k H1 H2 Ha g Hg. destruct (Ha g Hg) as [E1 [E2 [E3 [E4 [E5 E6]]]]]. repeat split; congruence. Qed.

Lemma agree_trans: forall k H1 H2 H3, agree k H1 H2 -> agree k H2 H3 -> agree k H1 H3.
Proof.
    intros k H1 H2 H3 Ha Hb g Hg. destruct (Ha g Hg) as [E1 [E2 [E3 [E4 [E5 E6]]]]].
    destruct (Hb g Hg) as [F1 [F2 [F3 [F4 [F5 F6]]]]]. repeat split; congruence.
Qed.

Lemma ref_ranked: forall k g, Nat.ltb (rank_of g) k = true -> rank_of g < k.
Proof. intros k g H. apply Nat.ltb_lt, H. Qed.

Section Agree.

Variables (k: nat) (H1 H2: Handlers).
Hypothesis Ha: agree k H1 H2.

Lemma top_const_h_agree: forall t, ranked_below k t = true -> top_const_h H1 t = top_const_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        try exact (proj1 (Ha g (ref_ranked k g H))).
    induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
    rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma mutability_of_h_agree: forall t, ranked_below k t = true -> mutability_of_h H1 t = mutability_of_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        try exact (proj1 (proj2 (Ha g (ref_ranked k g H)))).
    pose proof (top_const_h_agree (Intersection cs) H) as E. simpl in E. rewrite E.
    destruct (existsb (top_const_h H2) cs); [reflexivity|]. f_equal. clear E.
    induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
    rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma assignment_mutability_h_agree: forall t, ranked_below k t = true -> assignment_mutability_h H1 t = assignment_mutability_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        try exact (proj1 (proj2 (proj2 (Ha g (ref_ranked k g H))))).
    f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
    rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma is_nullable_h_agree: forall t, ranked_below k t = true -> is_nullable_h H1 t = is_nullable_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        exact (proj1 (proj2 (proj2 (proj2 (Ha g (ref_ranked k g H)))))).
Qed.

Lemma base_type_of_lower_bound_h_agree: forall t, ranked_below k t = true -> base_type_of_lower_bound_h H1 t = base_type_of_lower_bound_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        try exact (proj1 (proj2 (proj2 (proj2 (proj2 (Ha g (ref_ranked k g H))))))).
    f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
    rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma is_non_nullable_nothing_h_agree: forall t, ranked_below k t = true -> is_non_nullable_nothing_h H1 t = is_non_nullable_nothing_h H2 t.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity; try exact (IH n H);
        try exact (proj2 (proj2 (proj2 (proj2 (proj2 (Ha g (ref_ranked k g H))))))).
    f_equal.
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
    - unfold is_effectively_bottom_type_h. f_equal. clear IH.
      induction cs as [|c cs IHc]; [reflexivity|]. simpl in H |- *. apply andb_true_iff in H. destruct H as [Hc Hcs].
      rewrite (base_type_of_lower_bound_h_agree c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma with_mutability_h_ranked: forall H m t, ranked_below k t = true -> ranked_below k (with_mutability_h H m t) = true.
Proof.
    intros H. fix IH 2. intros m [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; simpl in Ht |- *; try exact Ht.
    - pose proof (IH m n Ht) as Hn. destruct (with_mutability_h H m n); exact Hn.
    - exact (IH m n Ht).
    - generalize (fold_left intersect_mutability (map (fun c => assignment_mutability_h H (with_mutability_h H m c)) cs) readonly).
      intros m'. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH m' c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma with_mutability_h_agree: forall m t, ranked_below k t = true -> with_mutability_h H1 m t = with_mutability_h H2 m t.
Proof.
    fix IH 2. intros m [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; simpl in Ht |- *; try reflexivity.
    - rewrite (IH m n Ht). reflexivity.
    - rewrite (IH m n Ht). reflexivity.
    - assert (Hcm: map (fun c => assignment_mutability_h H1 (with_mutability_h H1 m c)) cs
                 = map (fun c => assignment_mutability_h H2 (with_mutability_h H2 m c)) cs).
      { induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
        rewrite (IH m c Hc), (assignment_mutability_h_agree _ (with_mutability_h_ranked H2 m c Hc)), (IHc Hcs). reflexivity. }
      rewrite Hcm. generalize (fold_left intersect_mutability (map (fun c => assignment_mutability_h H2 (with_mutability_h H2 m c)) cs) readonly).
      intros m'. f_equal. clear Hcm. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH m' c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma without_null_h_ranked: forall H t, ranked_below k t = true -> ranked_below k (without_null_h H t) = true.
Proof. intros H. fix IH 1. intros [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; simpl in Ht |- *; try exact Ht; exact (IH n Ht). Qed.

Lemma without_null_h_agree: forall t, ranked_below k t = true -> without_null_h H1 t = without_null_h H2 t.
Proof.
    fix IH 1. intros [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; simpl in Ht |- *; try reflexivity.
    - exact (IH n Ht).
    - rewrite (proj1 (proj2 (proj2 (proj2 (Ha _ (ref_ranked k _ Ht)))))). reflexivity.
    - rewrite (IH n Ht). reflexivity.
Qed.

End Agree.

Lemma with_type_variables_ranked: forall k vs t, ranked_below k t = true -> ranked_below k (with_type_variables vs t) = true.
Proof.
    intros k [|v vs] t H; [exact H|]. unfold with_type_variables. revert t H. generalize (v :: vs) as ws. intros ws.
    fix IH 1. intros [mt c args|n|[gm nn p us]|me msg|w o n|[gm nn p us]|cs] Ht; simpl in Ht |- *; try exact Ht.
    - induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH a Hc), (IHa Hcs). reflexivity.
    - exact (IH n Ht).
    - destruct (existsb (param_eqb p) ws); exact Ht.
    - exact (IH n Ht).
    - induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Section Ranked.

Hypothesis ranked: bounds_ranked.

Lemma effective_bound_h_ranked: forall H g, ranked_below (rank_of g) (effective_bound_h H g) = true.
Proof.
    intros H g. unfold effective_bound_h. apply with_type_variables_ranked.
    pose proof (ranked (param_of g)) as Hd. fold (rank_of g) in Hd.
    destruct (given_mutability g) as [m|]; [pose proof (with_mutability_h_ranked (rank_of g) H m _ Hd) as Hd'; clear Hd; rename Hd' into Hd|];
        destruct (is_narrowed g); try exact Hd; apply without_null_h_ranked, Hd.
Qed.

Lemma effective_bound_h_agree: forall k H1 H2 g, agree k H1 H2 -> rank_of g <= k ->
    effective_bound_h H1 g = effective_bound_h H2 g.
Proof.
    intros k H1 H2 g Ha Hg. pose proof (agree_mono _ _ _ _ Hg Ha) as Ha'.
    unfold effective_bound_h. pose proof (ranked (param_of g)) as Hd. fold (rank_of g) in Hd. f_equal.
    destruct (given_mutability g) as [m|].
    - rewrite (with_mutability_h_agree _ _ _ Ha' m _ Hd). destruct (is_narrowed g); [|reflexivity].
      apply (without_null_h_agree _ _ _ Ha'), (with_mutability_h_ranked (rank_of g)), Hd.
    - destruct (is_narrowed g); [|reflexivity]. apply (without_null_h_agree _ _ _ Ha'), Hd.
Qed.

(* Each level gives what the levels above give, for the type parameters it is for *)
Lemma level_agree: forall j k, j <= k -> agree j (level j) (level k).
Proof.
    induction j as [|j IH]; intros k Hk g Hg; [lia|].
    destruct k as [|k]; [lia|]. assert (Hj: agree j (level j) (level k)) by (apply IH; lia).
    cbn [level h_top_const h_mutability h_assignment_mutability h_nullable h_base_type h_non_nullable_nothing].
    assert (Hg': rank_of g <= j) by lia.
    rewrite (effective_bound_h_agree j _ _ g Hj Hg').
    pose proof (effective_bound_h_ranked (level k) g) as Hr.
    pose proof (agree_mono _ _ _ _ Hg' Hj) as Hj'.
    repeat split.
    - exact (top_const_h_agree _ _ _ Hj' _ Hr).
    - exact (mutability_of_h_agree _ _ _ Hj' _ Hr).
    - exact (assignment_mutability_h_agree _ _ _ Hj' _ Hr).
    - exact (is_nullable_h_agree _ _ _ Hj' _ Hr).
    - exact (base_type_of_lower_bound_h_agree _ _ _ Hj' _ Hr).
    - exact (is_non_nullable_nothing_h_agree _ _ _ Hj' _ Hr).
Qed.

(* What a reference has of its effective bound is what level k gives, for k above its rank *)
Lemma top_handlers_agree: forall k, agree k top_handlers (level k).
Proof.
    intros k g Hg. destruct k as [|k]; [lia|].
    cbn [top_handlers level h_top_const h_mutability h_assignment_mutability h_nullable h_base_type h_non_nullable_nothing].
    unfold ref_top_const, ref_mutability, ref_assignment_mutability, ref_nullable, ref_base_type, ref_non_nullable_nothing, effective_bound.
    assert (Hj: agree (rank_of g) (level (rank_of g)) (level k)) by (apply level_agree; lia).
    rewrite (effective_bound_h_agree _ _ _ g Hj (le_n _)).
    pose proof (effective_bound_h_ranked (level k) g) as Hr.
    repeat split.
    - exact (top_const_h_agree _ _ _ Hj _ Hr).
    - exact (mutability_of_h_agree _ _ _ Hj _ Hr).
    - exact (assignment_mutability_h_agree _ _ _ Hj _ Hr).
    - exact (is_nullable_h_agree _ _ _ Hj _ Hr).
    - exact (base_type_of_lower_bound_h_agree _ _ _ Hj _ Hr).
    - exact (is_non_nullable_nothing_h_agree _ _ _ Hj _ Hr).
Qed.

End Ranked.

(* The functions above are those of the handlers for references, with what they have of their
   effective bounds *)
Lemma top_const_top: forall t, top_const t = top_const_h top_handlers t.
Proof. reflexivity. Qed.

Lemma mutability_of_top: forall t, mutability_of t = mutability_of_h top_handlers t.
Proof. reflexivity. Qed.

Lemma assignment_mutability_top: forall t, assignment_mutability t = assignment_mutability_h top_handlers t.
Proof. reflexivity. Qed.

Lemma is_nullable_top: forall t, is_nullable t = is_nullable_h top_handlers t.
Proof. reflexivity. Qed.

Lemma base_type_of_lower_bound_top: forall t, base_type_of_lower_bound t = base_type_of_lower_bound_h top_handlers t.
Proof. reflexivity. Qed.

Lemma is_non_nullable_nothing_top: forall t, is_non_nullable_nothing t = is_non_nullable_nothing_h top_handlers t.
Proof. reflexivity. Qed.

Lemma with_mutability_top: forall m t, with_mutability m t = with_mutability_h top_handlers m t.
Proof. reflexivity. Qed.

Lemma without_null_top: forall t, without_null t = without_null_h top_handlers t.
Proof. reflexivity. Qed.

Section Equations.

Hypothesis ranked: bounds_ranked.

(* GenericTypeReference.effectiveBound, as the functions above make it *)
Lemma effective_bound_eq: forall g,
    effective_bound g = with_type_variables (variables_of g)
        (let of_mutability := match given_mutability g with Some m => with_mutability m (parameter_bound env (param_of g)) | None => parameter_bound env (param_of g) end in
         if is_narrowed g then without_null of_mutability else of_mutability).
Proof.
    intros g. unfold effective_bound.
    rewrite (effective_bound_h_agree ranked (rank_of g) _ top_handlers g (agree_sym _ _ _ (top_handlers_agree ranked _)) (le_n _)).
    reflexivity.
Qed.

Lemma effective_bound_ranked: forall g, ranked_below (rank_of g) (effective_bound g) = true.
Proof. intros g. apply effective_bound_h_ranked, ranked. Qed.

Local Ltac through_bound ref top agree_lemma :=
    intros g; transitivity (ref g); [reflexivity|]; unfold ref; rewrite top;
    apply (agree_lemma _ _ _ (agree_sym _ _ _ (top_handlers_agree ranked _))), effective_bound_ranked.

(* A reference to a type parameter has the properties of its effective bound *)
Lemma top_const_generic: forall g, top_const (Generic g) = top_const (effective_bound g).
Proof. through_bound ref_top_const top_const_top top_const_h_agree. Qed.
Lemma top_const_type_variable: forall g, top_const (TypeVariable g) = top_const (effective_bound g).
Proof. through_bound ref_top_const top_const_top top_const_h_agree. Qed.
Lemma mutability_of_generic: forall g, mutability_of (Generic g) = mutability_of (effective_bound g).
Proof. through_bound ref_mutability mutability_of_top mutability_of_h_agree. Qed.
Lemma mutability_of_type_variable: forall g, mutability_of (TypeVariable g) = mutability_of (effective_bound g).
Proof. through_bound ref_mutability mutability_of_top mutability_of_h_agree. Qed.
Lemma assignment_mutability_generic: forall g, assignment_mutability (Generic g) = assignment_mutability (effective_bound g).
Proof. through_bound ref_assignment_mutability assignment_mutability_top assignment_mutability_h_agree. Qed.
Lemma assignment_mutability_type_variable: forall g, assignment_mutability (TypeVariable g) = assignment_mutability (effective_bound g).
Proof. through_bound ref_assignment_mutability assignment_mutability_top assignment_mutability_h_agree. Qed.
Lemma is_nullable_generic: forall g, is_nullable (Generic g) = is_nullable (effective_bound g).
Proof. through_bound ref_nullable is_nullable_top is_nullable_h_agree. Qed.
Lemma is_nullable_type_variable: forall g, is_nullable (TypeVariable g) = is_nullable (effective_bound g).
Proof. through_bound ref_nullable is_nullable_top is_nullable_h_agree. Qed.
Lemma base_type_generic: forall g, base_type_of_lower_bound (Generic g) = base_type_of_lower_bound (effective_bound g).
Proof. through_bound ref_base_type base_type_of_lower_bound_top base_type_of_lower_bound_h_agree. Qed.
Lemma base_type_type_variable: forall g, base_type_of_lower_bound (TypeVariable g) = base_type_of_lower_bound (effective_bound g).
Proof. through_bound ref_base_type base_type_of_lower_bound_top base_type_of_lower_bound_h_agree. Qed.
Lemma non_nullable_nothing_generic: forall g, is_non_nullable_nothing (Generic g) = is_non_nullable_nothing (effective_bound g).
Proof. through_bound ref_non_nullable_nothing is_non_nullable_nothing_top is_non_nullable_nothing_h_agree. Qed.
Lemma non_nullable_nothing_type_variable: forall g, is_non_nullable_nothing (TypeVariable g) = is_non_nullable_nothing (effective_bound g).
Proof. through_bound ref_non_nullable_nothing is_non_nullable_nothing_top is_non_nullable_nothing_h_agree. Qed.

Section Through.

Context {X: Type}.
Variable f_h: (GenericRef -> X) -> EType -> X.
Variable default: X.
(* f_h gives the same for types whose references it is given the same for *)
Hypothesis f_agree: forall k U1 U2, (forall g, rank_of g < k -> U1 g = U2 g) ->
    forall t, ranked_below k t = true -> f_h U1 t = f_h U2 t.

Lemma through_level_agree: forall j k, j <= k -> forall g, rank_of g < j -> through_level f_h default j g = through_level f_h default k g.
Proof.
    induction j as [|j IH]; intros k Hk g Hg; [lia|]. destruct k as [|k]; [lia|]. cbn [through_level].
    apply (f_agree j); [intros g' Hg'; apply IH; lia|].
    apply (ranked_below_mono (rank_of g)); [lia|apply effective_bound_ranked].
Qed.

(* A reference gives what its effective bound does *)
Lemma through_eq: forall g, through f_h default g = f_h (through f_h default) (effective_bound g).
Proof.
    intros g. unfold through at 1. cbn [through_level]. apply (f_agree (rank_of g)); [|apply effective_bound_ranked].
    intros g' Hg'. unfold through. symmetry. apply through_level_agree; lia.
Qed.

End Through.

Lemma instantiate_h_agree: forall k U1 U2, (forall g, rank_of g < k -> U1 g = U2 g) ->
    forall bindings t, ranked_below k t = true -> instantiate_h U1 bindings t = instantiate_h U2 bindings t.
Proof.
    intros k U1 U2 HU bindings. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Ht; simpl in Ht |- *; try reflexivity.
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Ha Has].
      rewrite (IH a Ha), (IHa Has). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - rewrite (HU _ (ref_ranked k _ Ht)). reflexivity.
    - rewrite (IH n Ht). reflexivity.
    - rewrite (HU _ (ref_ranked k _ Ht)). reflexivity.
    - f_equal. f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Ht |- *. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
      rewrite (IH c Hc), (IHc Hcs). reflexivity.
Qed.

Lemma instantiate_top: forall bindings t, instantiate bindings t = instantiate_h (instantiate_unbound bindings) bindings t.
Proof.
    intros bindings. fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs]; simpl; try reflexivity.
    - f_equal. induction args as [|a args IHa]; [reflexivity|]. simpl. rewrite (IH a), IHa. reflexivity.
    - rewrite (IH n). reflexivity.
    - rewrite (IH n). reflexivity.
    - f_equal. f_equal. induction cs as [|c cs IHc]; [reflexivity|]. simpl. rewrite (IH c), IHc. reflexivity.
Qed.

(* An unbound type parameter becomes its effective bound, instantiated *)
Lemma instantiate_unbound_eq: forall bindings g, instantiate_unbound bindings g = instantiate bindings (effective_bound g).
Proof.
    intros bindings g. rewrite instantiate_top. unfold instantiate_unbound at 1. rewrite through_eq; [reflexivity|].
    intros k U1 U2 HU t Ht. exact (instantiate_h_agree k U1 U2 HU bindings t Ht).
Qed.

(* Every type mentions type parameters of ranks below some k, so facts can be proven by induction on
   that k: for a reference, the facts about the types of lower ranks, its effective bound among them *)
Lemma ranked_exists: forall t, exists k, ranked_below k t = true.
Proof.
    fix IH 1. intros [m c args|n|g|me msg|v o n|g|cs].
    - induction args as [|a args IHa]; [exists 0; reflexivity|]. destruct (IH a) as [ka Ha]. destruct IHa as [kr Hr].
      exists (ka + kr). pose proof (ranked_below_mono kr (ka + kr) ltac:(lia) _ Hr) as Hr'. simpl in Hr' |- *.
      rewrite (ranked_below_mono ka (ka + kr) ltac:(lia) a Ha). exact Hr'.
    - exact (IH n).
    - exists (S (rank_of g)). simpl. apply Nat.ltb_lt. lia.
    - exists 0. reflexivity.
    - exact (IH n).
    - exists (S (rank_of g)). simpl. apply Nat.ltb_lt. lia.
    - induction cs as [|a cs IHa]; [exists 0; reflexivity|]. destruct (IH a) as [ka Ha]. destruct IHa as [kr Hr].
      exists (ka + kr). pose proof (ranked_below_mono kr (ka + kr) ltac:(lia) _ Hr) as Hr'. simpl in Hr' |- *.
      rewrite (ranked_below_mono ka (ka + kr) ltac:(lia) a Ha). exact Hr'.
Qed.

(* The bound of the parameter, with the mutability and `!` of the reference applied: the effective
   bound, but for the type variables *)
Definition adjusted_bound (g: GenericRef): EType :=
    let of_mutability := match given_mutability g with Some m => with_mutability m (parameter_bound env (param_of g)) | None => parameter_bound env (param_of g) end in
    if is_narrowed g then without_null of_mutability else of_mutability.

Lemma effective_bound_adjusted: forall g, effective_bound g = with_type_variables (variables_of g) (adjusted_bound g).
Proof. exact effective_bound_eq. Qed.

Lemma adjusted_bound_ranked: forall g, ranked_below (rank_of g) (adjusted_bound g) = true.
Proof.
    intros g. unfold adjusted_bound. pose proof (ranked (param_of g)) as Hd. fold (rank_of g) in Hd.
    destruct (given_mutability g) as [m|];
        [pose proof (with_mutability_h_ranked (rank_of g) top_handlers m _ Hd) as Hd'; clear Hd; rename Hd' into Hd|];
        destruct (is_narrowed g); try exact Hd; exact (without_null_h_ranked (rank_of g) top_handlers _ Hd).
Qed.

(* What the type variables of a reference don't change *)
Definition plain_properties (t: EType): Mutability * Mutability * bool * bool :=
    (mutability_of t, assignment_mutability t, is_nullable t, top_const t).

Lemma with_type_variables_keeps: forall vs t, plain_properties (with_type_variables vs t) = plain_properties t.
Proof.
    intros vs t. destruct (ranked_exists t) as [k Hk]. revert vs t Hk. induction k as [k IHk] using lt_wf_ind.
    assert (Href: forall g ws, rank_of g < k ->
        plain_properties (Generic (mkGenericRef (given_mutability g) (is_narrowed g) (param_of g) ws)) = plain_properties (Generic g)
        /\ plain_properties (TypeVariable (mkGenericRef (given_mutability g) (is_narrowed g) (param_of g) ws)) = plain_properties (Generic g)).
    { intros g ws Hg.
      assert (E: forall vs', plain_properties (with_type_variables vs' (adjusted_bound g)) = plain_properties (adjusted_bound g))
          by (intros vs'; exact (IHk (rank_of g) Hg vs' _ (adjusted_bound_ranked g))).
      assert (Pg: forall h, plain_properties (Generic h) = plain_properties (effective_bound h))
          by (intros h; unfold plain_properties; rewrite mutability_of_generic, assignment_mutability_generic, is_nullable_generic, top_const_generic; reflexivity).
      assert (Pv: forall h, plain_properties (TypeVariable h) = plain_properties (effective_bound h))
          by (intros h; unfold plain_properties; rewrite mutability_of_type_variable, assignment_mutability_type_variable,
              is_nullable_type_variable, top_const_type_variable; reflexivity).
      rewrite !Pg, !Pv, !effective_bound_adjusted. destruct g as [gm nn p us]. cbn [variables_of given_mutability is_narrowed param_of].
      change (adjusted_bound (mkGenericRef gm nn p ws)) with (adjusted_bound (mkGenericRef gm nn p us)).
      rewrite !E. split; reflexivity. }
    intros [|v vs] t Ht; [reflexivity|]. unfold with_type_variables. revert t Ht. generalize (v :: vs) as ws. intros ws.
    fix IH 1. intros [m c args|n|[gm nn p us]|me msg|w o n|[gm nn p us]|cs] Ht; simpl in Ht.
    - reflexivity.
    - pose proof (IH n Ht) as E. unfold plain_properties in E |- *. simpl. injection E as E1 E2 E3 E4. rewrite E1, E2, E4. reflexivity.
    - cbn [with_type_variables_in]. pose proof (Href (mkGenericRef gm nn p us) (us ++ ws) (ref_ranked k _ Ht)) as [E1 E2].
      destruct (existsb (param_eqb p) ws); [exact E2|exact E1].
    - reflexivity.
    - pose proof (IH n Ht) as E. unfold plain_properties in E |- *. simpl. injection E as E1 E2 E3 E4. rewrite E1, E2, E3, E4. reflexivity.
    - cbn [with_type_variables_in]. pose proof (Href (mkGenericRef gm nn p us) (us ++ ws) (ref_ranked k _ Ht)) as [_ E2].
      pose proof (Href (mkGenericRef gm nn p us) us (ref_ranked k _ Ht)) as [_ E3]. exact (eq_trans E2 (eq_sym E3)).
    - assert (Hall: forall c, In c cs -> plain_properties (with_type_variables_in ws c) = plain_properties c).
      { clear -IH Ht. induction cs as [|c cs IHc]; intros c' Hin; [destruct Hin|]. simpl in Ht. apply andb_true_iff in Ht. destruct Ht as [Hc Hcs].
        destruct Hin as [<-|Hin]; [exact (IH c Hc)|exact (IHc Hcs c' Hin)]. }
      unfold plain_properties. cbn [with_type_variables_in mutability_of assignment_mutability is_nullable top_const].
      assert (Etc: existsb top_const (map (with_type_variables_in ws) cs) = existsb top_const cs).
      { clear -Hall. induction cs as [|c cs IHc]; [reflexivity|]. simpl. pose proof (Hall c (or_introl eq_refl)) as E.
        unfold plain_properties in E. injection E as _ _ _ E. rewrite E, IHc; [reflexivity|]. intros c' Hc'. apply Hall. right. exact Hc'. }
      assert (Em: map mutability_of (map (with_type_variables_in ws) cs) = map mutability_of cs).
      { clear -Hall. induction cs as [|c cs IHc]; [reflexivity|]. simpl. pose proof (Hall c (or_introl eq_refl)) as E.
        unfold plain_properties in E. injection E as E _ _ _. rewrite E, IHc; [reflexivity|]. intros c' Hc'. apply Hall. right. exact Hc'. }
      assert (Ea: map assignment_mutability (map (with_type_variables_in ws) cs) = map assignment_mutability cs).
      { clear -Hall. induction cs as [|c cs IHc]; [reflexivity|]. simpl. pose proof (Hall c (or_introl eq_refl)) as E.
        unfold plain_properties in E. injection E as _ E _ _. rewrite E, IHc; [reflexivity|]. intros c' Hc'. apply Hall. right. exact Hc'. }
      rewrite Etc, Em, Ea. reflexivity.
Qed.

(* A reference as written, `T`, without type variables: the bound of the parameter *)
Lemma effective_bound_plain: forall p, effective_bound (mkGenericRef None false p []) = parameter_bound env p.
Proof. intros p. rewrite effective_bound_eq. reflexivity. Qed.

(* `!` leaves a type that isn't nullable as it is, and applied twice, it is applied once *)
Lemma without_null_unchanged: forall t, is_nullable t = false -> without_null t = t.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] H; simpl in H |- *; try reflexivity.
    - discriminate H.
    - rewrite H, orb_false_r. reflexivity.
    - rewrite (IH n H). reflexivity.
Qed.

Lemma without_null_twice_any: forall t, without_null (without_null t) = without_null t.
Proof.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs]; simpl; try reflexivity.
    - exact (IH n).
    - destruct nn; [reflexivity|]. cbn [orb]. destruct (ref_nullable (mkGenericRef gm false p vs)) eqn:E; [reflexivity|].
      rewrite E. reflexivity.
    - rewrite (IH n). reflexivity.
Qed.

(* `T!` has the bound of T without null, where T has no type variables *)
Lemma effective_bound_narrowed: forall gm nn p,
    effective_bound (mkGenericRef gm (nn || is_nullable (Generic (mkGenericRef gm nn p []))) p [])
    = without_null (effective_bound (mkGenericRef gm nn p [])).
Proof.
    intros gm nn p. rewrite is_nullable_generic, !effective_bound_eq. cbn [with_type_variables variables_of given_mutability is_narrowed param_of].
    set (x := match gm with Some m => with_mutability m (parameter_bound env p) | None => parameter_bound env p end).
    destruct nn; cbn [orb]; [symmetry; apply without_null_twice_any|].
    destruct (is_nullable x) eqn:E; [reflexivity|]. symmetry. exact (without_null_unchanged x E).
Qed.

Lemma with_type_variables_top_const: forall vs t, top_const (with_type_variables vs t) = top_const t.
Proof. intros vs t. pose proof (with_type_variables_keeps vs t) as E. unfold plain_properties in E. injection E as _ _ _ E. exact E. Qed.

Lemma with_type_variables_nullable: forall vs t, is_nullable (with_type_variables vs t) = is_nullable t.
Proof. intros vs t. pose proof (with_type_variables_keeps vs t) as E. unfold plain_properties in E. injection E as _ _ E _. exact E. Qed.

(* `!` keeps whether a type is const *)
Lemma top_const_without_null: forall t, top_const (without_null t) = top_const t.
Proof.
    intros t. destruct (ranked_exists t) as [k Hk]. revert t Hk. induction k as [k IHk] using lt_wf_ind.
    fix IH 1. intros [m c args|n|[gm nn p vs]|me msg|v o n|g|cs] Hk; try reflexivity.
    - exact (IH n Hk).
    - cbn [without_null]. rewrite !top_const_generic, !effective_bound_adjusted, !with_type_variables_top_const.
      unfold adjusted_bound. cbn [given_mutability is_narrowed param_of].
      destruct nn; [reflexivity|]. cbn [orb]. destruct (ref_nullable _); [|reflexivity].
      apply (IHk _ (ref_ranked k _ Hk)). exact (adjusted_bound_ranked (mkGenericRef gm false p vs)).
    - exact (IH n Hk).
Qed.

(* Applying a mutability keeps whether a type is const, and whether it is nullable, with `!` or not *)
Lemma with_mutability_keeps: forall m t,
    top_const (with_mutability m t) = top_const t /\ is_nullable (with_mutability m t) = is_nullable t
    /\ is_nullable (without_null (with_mutability m t)) = is_nullable (without_null t).
Proof.
    intros m t. destruct (ranked_exists t) as [k Hk]. revert m t Hk. induction k as [k IHk] using lt_wf_ind.
    (* references of whatever given mutability to the same parameter *)
    assert (Href: forall gm1 gm2 nn p vs, rank_of (mkGenericRef gm1 nn p vs) < k ->
        top_const (Generic (mkGenericRef gm1 nn p vs)) = top_const (Generic (mkGenericRef gm2 nn p vs))
        /\ is_nullable (Generic (mkGenericRef gm1 nn p vs)) = is_nullable (Generic (mkGenericRef gm2 nn p vs))
        /\ (forall nn', top_const (Generic (mkGenericRef gm1 nn' p vs)) = top_const (Generic (mkGenericRef gm1 nn p vs)))).
    { intros gm1 gm2 nn p vs Hg.
      assert (Hd: ranked_below (rank_of (mkGenericRef gm1 nn p vs)) (parameter_bound env p) = true) by exact (ranked p).
      assert (Hadj: forall gm, (forall nn', top_const (adjusted_bound (mkGenericRef gm nn' p vs)) = top_const (parameter_bound env p))
          /\ is_nullable (adjusted_bound (mkGenericRef gm nn p vs))
             = (if nn then is_nullable (without_null (parameter_bound env p)) else is_nullable (parameter_bound env p))).
      { intros [m'|]; unfold adjusted_bound; cbn [given_mutability is_narrowed param_of].
        - destruct (IHk _ Hg m' _ Hd) as [Ht [Hn Hwn]]. split; [intros [|]; [rewrite top_const_without_null|]; exact Ht|].
          destruct nn; [exact Hwn|exact Hn].
        - split; [intros [|]; [rewrite top_const_without_null|]; reflexivity|]. destruct nn; reflexivity. }
      rewrite !top_const_generic, !is_nullable_generic, !effective_bound_adjusted, !with_type_variables_top_const, !with_type_variables_nullable.
      cbn [variables_of]. destruct (Hadj gm1) as [Ht1 Hn1]. destruct (Hadj gm2) as [Ht2 Hn2].
      split; [rewrite Ht1, Ht2; reflexivity|]. split; [rewrite Hn1, Hn2; reflexivity|].
      intros nn'. rewrite !top_const_generic, !effective_bound_adjusted, !with_type_variables_top_const. cbn [variables_of].
      rewrite !Ht1. reflexivity. }
    fix IH 2. intros m [mt c args|n|[gm nn p vs]|me msg|v o n|[gm nn p vs]|cs] Hk.
    - repeat split.
    - destruct (IH m n Hk) as [Ht [Hn Hwn]]. cbn [with_mutability].
      assert (Hr: forall x, top_const (rewrap_nullable x) = top_const x /\ is_nullable (rewrap_nullable x) = true
          /\ without_null (rewrap_nullable x) = without_null x) by (intros [| | | | | |]; repeat split).
      destruct (Hr (with_mutability m n)) as [Hr1 [Hr2 Hr3]]. rewrite Hr1, Hr2, Hr3. repeat split; [exact Ht|exact Hwn].
    - pose proof (ref_ranked k _ Hk) as Hg. destruct (Href (Some m) gm nn p vs Hg) as [Ht [Hn _]].
      cbn [with_mutability without_null]. split; [exact Ht|]. split; [exact Hn|].
      change (ref_nullable (mkGenericRef (Some m) nn p vs)) with (is_nullable (Generic (mkGenericRef (Some m) nn p vs))).
      change (ref_nullable (mkGenericRef gm nn p vs)) with (is_nullable (Generic (mkGenericRef gm nn p vs))). rewrite Hn.
      destruct (nn || is_nullable (Generic (mkGenericRef gm nn p vs))) eqn:E.
      + rewrite !is_nullable_generic, !effective_bound_adjusted, !with_type_variables_nullable. cbn [variables_of].
        unfold adjusted_bound. cbn [given_mutability is_narrowed param_of].
        destruct gm as [m0|]; [|exact (proj2 (proj2 (IHk _ Hg m _ (ranked p))))].
        rewrite (proj2 (proj2 (IHk _ Hg m _ (ranked p)))). symmetry. exact (proj2 (proj2 (IHk _ Hg m0 _ (ranked p)))).
      + apply orb_false_iff in E. destruct E as [-> E]. rewrite ?Hn, ?E. reflexivity.
    - repeat split.
    - destruct (IH m n Hk) as [Ht [Hn Hwn]]. cbn [with_mutability without_null top_const is_nullable]. repeat split; assumption.
    - pose proof (ref_ranked k _ Hk) as Hg.
      assert (E: forall gm', top_const (TypeVariable (mkGenericRef gm' nn p vs)) = top_const (Generic (mkGenericRef gm' nn p vs))
          /\ is_nullable (TypeVariable (mkGenericRef gm' nn p vs)) = is_nullable (Generic (mkGenericRef gm' nn p vs)))
          by (intros gm'; split; reflexivity).
      destruct (Href (Some m) gm nn p vs Hg) as [Ht [Hn _]]. cbn [with_mutability without_null].
      destruct (E (Some m)) as [E1 E2]. destruct (E gm) as [E3 E4]. rewrite E1, E2, E3, E4. repeat split; assumption.
    - cbn [with_mutability top_const is_nullable without_null]. split; [|split; reflexivity].
      generalize (fold_left intersect_mutability (map (fun c => assignment_mutability (with_mutability m c)) cs) readonly).
      intros m'. simpl in Hk. clear -IH Hk. induction cs as [|c cs IHc]; [reflexivity|]. simpl in Hk |- *.
      apply andb_true_iff in Hk. destruct Hk as [Hc Hcs]. rewrite (proj1 (IH m' c Hc)), (IHc Hcs). reflexivity.
Qed.

End Equations.

End Subtyping.

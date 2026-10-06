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
 *   helpful diagnostic, this doesn't. TypeUnification.plusExactBinding, which only serves explicit
 *   type arguments and tells its diagnostics apart, is left out.
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

From Stdlib Require Import List Bool Arith.
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

(* BoundTypeReference.mutability *)
Fixpoint mutability_of (t: EType): Mutability :=
    match t with
    | RootResolved m c _ =>
        if is_core_scalar (declaration_of env c) then immutable else or_readonly m
    | Nullable n => mutability_of n
    | Generic (mkGenericRef given _ bound)
    | TypeVariable (mkGenericRef given _ bound) =>
        let bound_mutability := mutability_of bound in
        match given with
        | Some m => if Model.is_subtype_of m bound_mutability then m else bound_mutability
        | None => bound_mutability
        end
    | Error m _ => or_readonly m
    | TypeArgument _ _ n => mutability_of n
    (* readonly is the neutral element of intersect_mutability *)
    | Intersection components => fold_left intersect_mutability (map mutability_of components) readonly
    end.

(* BoundTypeReference.isNullable *)
Fixpoint is_nullable (t: EType): bool :=
    match t with
    | RootResolved _ _ _ => false
    | Nullable _ => true
    | Generic (mkGenericRef _ _ bound)
    | TypeVariable (mkGenericRef _ _ bound) => is_nullable bound
    | Error _ _ => false
    | TypeArgument _ _ n => is_nullable n
    | Intersection _ => false
    end.

(* BoundTypeReference.baseTypeOfLowerBound *)
Fixpoint base_type_of_lower_bound (t: EType): Class :=
    match t with
    | RootResolved _ c _ => c
    | Nullable n => base_type_of_lower_bound n
    | Generic (mkGenericRef _ _ bound)
    | TypeVariable (mkGenericRef _ _ bound) => base_type_of_lower_bound bound
    | Error _ _ => nothing
    | TypeArgument _ _ n => base_type_of_lower_bound n
    | Intersection components => closest_common_super_class env (map base_type_of_lower_bound components)
    end.

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
    | Generic (mkGenericRef _ p' _) => param_eqb p p'
    | Nullable n => is_generic_of p n
    | _ => false
    end.

(* BoundTypeReference.hasSameBaseTypeAs *)
Fixpoint has_same_base_type_as (t other: EType): bool :=
    match t with
    | RootResolved _ c _ => has_base_type c other
    | Nullable n => has_same_base_type_as n other
    | Generic (mkGenericRef _ p _) => is_generic_of p other
    | Error _ _ => true
    | TypeArgument _ _ n => has_same_base_type_as n other
    (* Kotlin compares for equality; comparing the parameters is close enough for base types *)
    | TypeVariable (mkGenericRef _ p _) =>
        match other with TypeVariable (mkGenericRef _ p' _) => param_eqb p p' | _ => false end
    | Intersection components => existsb (fun c => has_same_base_type_as c other) components
    end.

(* whether `f` holds for any two distinct elements of `l`, like twoElementPermutationsUnordered().any(f) *)
Fixpoint exists_unordered_pair {A: Type} (f: A -> A -> bool) (l: list A): bool :=
    match l with
    | [] => false
    | x :: rest => existsb (f x) rest || exists_unordered_pair f rest
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
    | Generic (mkGenericRef _ _ bound)
    | TypeVariable (mkGenericRef _ _ bound) => is_non_nullable_nothing bound
    | Error _ _ => false
    | TypeArgument _ _ n => is_non_nullable_nothing n
    | Intersection components =>
        existsb is_non_nullable_nothing components || is_effectively_bottom_type components
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

(* ---------------------------------------------------------------------------------------------- *)
(* Instantiating type parameters                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* NullableTypeReference.rewrap: nullable, without nesting nullability *)
Definition rewrap_nullable (t: EType): EType :=
    match t with
    | Nullable _ => t
    | _ => Nullable t
    end.

(* BoundTypeReference.withMutabilityUnionedWith *)
Fixpoint with_mutability_unioned_with (m: Mutability) (t: EType): EType :=
    match t with
    | RootResolved _ c arguments =>
        let combined := union (mutability_of t) m in
        if Mutability_beq combined (mutability_of t) then t else RootResolved (Some combined) c arguments
    | Nullable n => rewrap_nullable (with_mutability_unioned_with m n)
    | Generic (mkGenericRef gm p bound) => Generic (mkGenericRef gm p (with_mutability_unioned_with m bound))
    | TypeVariable (mkGenericRef gm p bound) => TypeVariable (mkGenericRef gm p (with_mutability_unioned_with m bound))
    (* the model's ErroneousType has no type arguments that it could default the mutability of *)
    | Error _ _ => t
    | TypeArgument v o n =>
        if Mutability_beq (mutability_of n) m then t else TypeArgument v o (with_mutability_unioned_with m n)
    | Intersection components => Intersection (map (with_mutability_unioned_with m) components)
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

(*
 * BoundTypeReference.instantiateAllParameters, extended with ownership. Where it deviates:
 * - TypeUnification.getFinalValueFor instantiates the free variables in a binding. The bindings here
 *   are those of a type reference (TypeUnification.forSubstitution), in which type variables belong to
 *   another inference; they stay as they are (TypeVariable.instantiateFreeVariables), so that unifying
 *   with the instantiated type constrains them. They do occur: in `fn f<T>(c: Consumer<in MyLst<T>>)`
 *   called with a `Consumer<in Lst<X>>`, `MyLst<T>` becomes the assignee of `Lst<X>`, with T under
 *   inference. So this is left out.
 * - A type parameter without a binding is replaced by its bound; Kotlin uses the declared bound,
 *   this the effective bound of the reference.
 * - BoundIntersectionTypeReference simplifies the instantiated intersection, this doesn't.
 *)
Fixpoint instantiate (bindings: Bindings) (t: EType): EType :=
    match t with
    | RootResolved m c arguments => RootResolved m c (map (instantiate bindings) arguments)
    | Nullable n => rewrap_nullable (instantiate bindings n)
    | Generic (mkGenericRef given p bound) =>
        let final_value :=
            match lookup_binding bindings p with
            | Some argument => argument
            | None => instantiate bindings bound
            end in
        match given with
        | Some _ => with_mutability_unioned_with (mutability_of t) final_value
        | None => final_value
        end
    | Error _ _ => t
    (* BoundTypeArgument.instantiateAllParameters: when the nested type becomes a type argument of its
       own (a type parameter replaced by its binding), their variances merge; `out T` with T bound to
       `out X` is `out X`, and only opposite variances leave nothing but the top type *)
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
                    (if is_nullable_instantiated then Nullable nested_type else nested_type)
            else
                let top := RootResolved (Some (intersect_mutability (mutability_of n) (mutability_of n_non_null))) any [] in
                TypeArgument output o' (if is_nullable n || is_nullable_instantiated then Nullable top else top)
        | _ => TypeArgument v o' (if is_nullable_instantiated then Nullable n_non_null else n_non_null)
        end
    (* TypeVariable.instantiateAllParameters *)
    | TypeVariable (mkGenericRef _ p bound) =>
        match lookup_binding bindings p with
        | Some argument => argument
        | None => instantiate bindings bound
        end
    | Intersection components => Intersection (map (instantiate bindings) components)
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
Definition for_inference_of (parameters: list (TypeParameterId * EType)): Unification :=
    Ongoing (map (fun '(p, bound) => (p, mkVariableState bound bound bottom_type false)) parameters).

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
            (mkVariableState (static_upper_bound state) new_upper_bound (lower_bound state) false)))
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
            (mkVariableState (static_upper_bound state) (upper_bound state) new_lower_bound false)))
        end
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

(* RootResolvedTypeReference.unify *)
Definition unify_root_resolved (unify: UnifyFn) (self: EType) (base_type: Class) (arguments: list EType) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | RootResolved _ assignee_base_type assignee_arguments =>
        if negb (base_type_is_subtype_of assignee_base_type base_type) then Some Failed else
        if negb (Model.is_subtype_of (mutability_of assignee) (mutability_of self)) then Some Failed else
        (* Nothing is a subtype of every other possible type, which cannot be denoted in source code *)
        if class_eqb assignee_base_type nothing then Some (Ongoing states) else
        let normalized_assignee_arguments :=
            if class_eqb assignee_base_type base_type
            then assignee_arguments
            else parameterized_supertype_arguments assignee_base_type assignee_arguments base_type in
        unify_arguments unify arguments normalized_assignee_arguments states
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | Generic (mkGenericRef _ _ bound) => unify self bound (Ongoing states)
    | TypeArgument _ _ type => unify self type (Ongoing states)
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
    (* a possibly null value to a non-null reference *)
    | Nullable _ => Some Failed
    | Intersection components => intersection_flipped_unify unify self components states
    end.

(* NullableTypeReference.unify *)
Definition unify_nullable (unify: UnifyFn) (self nested assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | Nullable assignee_nested => unify nested assignee_nested (Ongoing states)
    | TypeArgument _ _ type => unify self type (Ongoing states)
    | Generic (mkGenericRef _ _ bound) =>
        match nested with
        | Generic _ | TypeArgument _ _ _ => unify nested assignee (Ongoing states)
        | _ => unify self bound (Ongoing states)
        end
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
    | _ => unify nested assignee (Ongoing states)
    end.

(* GenericTypeReference.isSubtypeOf: whether t, a Generic, is the generic `other`, or bounded by it *)
Fixpoint generic_is_subtype_of (t: EType) (other: TypeParameterId) (other_mutability: Mutability): bool :=
    match t with
    | Generic (mkGenericRef _ p bound) =>
        if param_eqb p other
        then Model.is_subtype_of (mutability_of t) other_mutability
        else generic_is_subtype_of bound other other_mutability
    | _ => false
    end.

(* GenericTypeReference.unify *)
Definition unify_generic (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    (* a possibly null value to a non-nullable reference *)
    | Nullable _ => Some Failed
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | RootResolved _ _ _ =>
        if is_non_nullable_nothing assignee then Some (Ongoing states) else Some Failed
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
    | TypeArgument variance _ type =>
        match variance with
        | output | invariant => unify self type (Ongoing states)
        | input => unify self top_type (Ongoing states)
        end
    | Generic _ =>
        if generic_is_subtype_of assignee parameter (mutability_of self) then Some (Ongoing states) else Some Failed
    | Intersection components => intersection_flipped_unify unify self components states
    end.

(* ErroneousType.unify: acts like Any *)
Definition unify_erroneous (unify: UnifyFn) (self: EType) (m: Mutability) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
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
        (* the target uses the type both in IN and OUT fashion, the source must match exactly *)
        | invariant, invariant =>
            let* carry2 := unify type assignee_type (Ongoing states) in
            unify assignee_type type carry2
        | invariant, _ => Some Failed
        | output, output
        | output, invariant => unify type assignee_type (Ongoing states)
        | output, input => Some Failed
        (* IN variance reverses the hierarchy direction *)
        | input, input
        | input, invariant => unify assignee_type type (Ongoing states)
        | input, output => Some Failed
        end
    | Generic _ => unify type assignee (Ongoing states)
    | Intersection components => intersection_flipped_unify unify self components states
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
    end.

(* TypeVariable.unify *)
Definition unify_type_variable (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (states: VariableStates): option Unification :=
    match assignee with
    | RootResolved _ _ _
    | Generic _
    | Intersection _
    | TypeArgument _ _ _ => plus_supertype_constraint unify states parameter assignee
    | Error m _ => unify self (as_nothing (or_readonly m)) (Ongoing states)
    (* Kotlin throws an InternalCompilerError *)
    | TypeVariable _ => None
    | Nullable nested =>
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
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p states
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
            fold_unify (fun inner component => unify component new_assignee inner) var_components (Ongoing states3)
        end
    end.

(* BoundTypeReference.unify, dispatching on the class of the target *)
Definition unify_step (unify: UnifyFn) (target assignee: EType) (states: VariableStates): option Unification :=
    match target with
    | RootResolved _ base_type arguments => unify_root_resolved unify target base_type arguments assignee states
    | Nullable nested => unify_nullable unify target nested assignee states
    | Generic (mkGenericRef _ parameter _) => unify_generic unify target parameter assignee states
    | Error m _ => unify_erroneous unify target (or_readonly m) assignee states
    | TypeArgument variance ownership type => unify_type_argument unify target variance ownership type assignee states
    | TypeVariable (mkGenericRef _ parameter _) => unify_type_variable unify target parameter assignee states
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
        | match goal with x: _ * _ |- _ => destruct x end; apply Hfg; assumption ].

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
    is_core_scalar (declaration_of env nothing) = false ->
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

End Subtyping.

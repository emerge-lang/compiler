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
 * - Everything that unify only consumes, rather than decides, is a section variable: the class
 *   declarations, what is derived from them (the transitive supertypes, their type arguments), and
 *   the lattice operations the inference uses (closestCommonSupertypeWith, intersect). They are
 *   translations of their own.
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

(* the declaration of every class *)
Variable declaration_of: Class -> ClassDecl.

(* BoundBaseType.Kind.allowsSubtypes *)
Definition allows_subtypes (c: Class): bool :=
    match kind (declaration_of c) with
    | class_kind => false
    | interface_kind => true
    end.

(* The keys of superTypes.preprocessedInheritanceTree.parameterizedSupertypes: all the transitive
   supertypes of a class, following the supertypes of declaration_of, except Any. *)
Variable supertypes_of: Class -> list Class.

(* BoundBaseType.closestCommonSupertypeOf *)
Variable closest_common_super_class: list Class -> Class.

(*
 * Given a class `sub` with type arguments `sub_arguments` and one of its supertypes `super`
 * (never `sub` itself, nor `nothing`): the type arguments `super` has as a supertype of that
 * reference. That is RootResolvedTypeReference.getInstantiatedSupertype, i.e.
 * `baseType.superTypes.getParameterizedSupertype(super).instantiateAllParameters(inherentTypeBindings)`.
 *)
Variable parameterized_supertype_arguments: Class -> list EType -> Class -> list EType.

(* BoundTypeReference.closestCommonSupertypeWith *)
Variable closest_common_supertype_with: EType -> EType -> EType.

(* BoundIntersectionTypeReference.Companion.intersect *)
Variable intersect: EType -> EType -> EType.

(* ---------------------------------------------------------------------------------------------- *)
(* Properties of types that unify reads                                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* BoundBaseType.isSubtypeOf *)
Definition base_type_is_subtype_of (sub super: Class): bool :=
    if class_eqb super sub then true else
    if class_eqb super any then true else
    if class_eqb super nothing then false else
    if class_eqb sub nothing then true else
    existsb (class_eqb super) (supertypes_of sub).

(* the default mutability of a reference, `mutability ?: READONLY` *)
Definition or_readonly (m: option Mutability): Mutability :=
    match m with Some m => m | None => readonly end.

(* BoundTypeReference.mutability *)
Fixpoint mutability_of (t: EType): Mutability :=
    match t with
    | RootResolved m c _ =>
        if is_core_scalar (declaration_of c) then immutable else or_readonly m
    | Nullable n => mutability_of n
    | Generic (mkGenericRef given _ bound)
    | TypeVariable (mkGenericRef given _ bound) =>
        let bound_mutability := mutability_of bound in
        match given with
        | Some m => if Model.is_subtype_of m bound_mutability then m else bound_mutability
        | None => bound_mutability
        end
    | Error m _ => or_readonly m
    | TypeArgument _ n => mutability_of n
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
    | TypeArgument _ n => is_nullable n
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
    | TypeArgument _ n => base_type_of_lower_bound n
    | Intersection components => closest_common_super_class (map base_type_of_lower_bound components)
    end.

(* RootResolvedTypeReference.hasSameBaseTypeAs *)
Fixpoint has_base_type (c: Class) (other: EType): bool :=
    match other with
    | RootResolved _ c' _ => class_eqb c c'
    | Nullable n => has_base_type c n
    | TypeArgument _ n => has_base_type c n
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
    | TypeArgument _ n => has_same_base_type_as n other
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
    | TypeArgument _ n => is_non_nullable_nothing n
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
(* TypeUnification                                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

(* TypeUnification.VariableState *)
Record VariableState := mkVariableState {
    static_upper_bound: EType;
    upper_bound: EType;
    lower_bound: EType;
    is_exact: bool;
}.

(*
 * TypeUnification. Its diagnostics are reduced to whether there are any: all the diagnostics unify
 * produces are errors, and what matters here is whether an assignment holds, not why it doesn't.
 *)
Record Unification := mkUnification {
    variable_states: list (TypeParameterId * VariableState);
    failed: bool;
}.

(* TypeUnification.EMPTY *)
Definition empty_unification: Unification := mkUnification [] false.

(* TypeUnification.forInferenceOf; the bounds are expected with their type variables already in
   place (`it.bound.withTypeVariables(parameters)`) *)
Definition for_inference_of (parameters: list (TypeParameterId * EType)): Unification :=
    mkUnification
        (map (fun '(p, bound) => (p, mkVariableState bound bound bottom_type false)) parameters)
        false.

Fixpoint lookup_state (states: list (TypeParameterId * VariableState)) (p: TypeParameterId): option VariableState :=
    match states with
    | [] => None
    | (p', s) :: rest => if param_eqb p p' then Some s else lookup_state rest p
    end.

(* `states + mapOf(p to s)` *)
Definition set_state (states: list (TypeParameterId * VariableState)) (p: TypeParameterId) (s: VariableState) :=
    (p, s) :: filter (fun '(p', _) => negb (param_eqb p p')) states.

(* TypeUnification.plusDiagnostic, with an error *)
Definition fail (u: Unification): Unification := mkUnification (variable_states u) true.

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
 * The functions below are only ever given a carry that hasn't failed (see unify), so any failure
 * of a result is a new one: `failed result` stands for Kotlin's `result.getErrorsNotIn(carry).any()`.
 *)

(* TypeUnification.plusSubtypeConstraint: parameter must be assignable to upper *)
Definition plus_subtype_constraint (unify: UnifyFn) (carry: Unification) (parameter: TypeParameterId) (upper: EType): option Unification :=
    match lookup_state (variable_states carry) parameter with
    (* TypeVariableNotUnderInferenceException *)
    | None => None
    | Some state =>
        if is_exact state then unify upper (upper_bound state) carry else
        let new_upper_bound := intersect (upper_bound state) upper in
        (* Incompatible constraints. Kotlin also unifies with the static upper bound here, to tell
           whether that or another constraint is to blame; it fails either way. *)
        if is_non_nullable_nothing new_upper_bound then Some (fail carry) else
        let* with_lower_bound := unify new_upper_bound (lower_bound state) carry in
        if failed with_lower_bound then Some (fail carry) else
        Some (mkUnification
            (set_state (variable_states with_lower_bound) parameter
                (mkVariableState (static_upper_bound state) new_upper_bound (lower_bound state) false))
            (failed carry))
    end.

(* TypeUnification.plusSupertypeConstraint: lower must be assignable to parameter *)
Definition plus_supertype_constraint (unify: UnifyFn) (carry: Unification) (parameter: TypeParameterId) (lower: EType): option Unification :=
    match lookup_state (variable_states carry) parameter with
    (* TypeVariableNotUnderInferenceException *)
    | None => None
    | Some state =>
        if is_exact state then unify (lower_bound state) lower carry else
        let new_lower_bound := closest_common_supertype_with (lower_bound state) lower in
        let* with_upper_bound := unify (upper_bound state) new_lower_bound carry in
        (* Incompatible constraints. Kotlin also unifies with the static upper bound here, to tell
           whether that or another constraint is to blame; it fails either way. *)
        if failed with_upper_bound then Some (fail carry) else
        Some (mkUnification
            (set_state (variable_states with_upper_bound) parameter
                (mkVariableState (static_upper_bound state) (upper_bound state) new_lower_bound false))
            (failed carry))
    end.

(* TypeVariable.flippedUnify: the variable is the assignee *)
Definition type_variable_flipped_unify (unify: UnifyFn) (target: EType) (parameter: TypeParameterId) (carry: Unification): option Unification :=
    plus_subtype_constraint unify carry parameter target.

(* The first of the candidates for which attempt doesn't fail, and the result of the attempt;
   Some None if there is none. Like Kotlin's firstOrNull on a sequence, it stops at that one. *)
Fixpoint find_first (attempt: EType -> option Unification) (candidates: list EType): option (option (EType * Unification)) :=
    match candidates with
    | [] => Some None
    | candidate :: rest =>
        let* result := attempt candidate in
        if failed result then find_first attempt rest else Some (Some (candidate, result))
    end.

(* BoundIntersectionTypeReference.flippedUnify: the intersection is the assignee; the first
   component that is assignable to target wins *)
Definition intersection_flipped_unify (unify: UnifyFn) (target: EType) (components: list EType) (carry: Unification): option Unification :=
    let* first := find_first (fun component => unify target component carry) components in
    match first with
    | Some (_, success) => Some success
    | None => Some (fail carry)
    end.

(* fold_left, for a function that may not give an answer *)
Fixpoint fold_unify {A: Type} (f: Unification -> A -> option Unification) (l: list A) (carry: Unification): option Unification :=
    match l with
    | [] => Some carry
    | x :: rest => let* next := f carry x in fold_unify f rest next
    end.

Definition unify_arguments (unify: UnifyFn) (targets assignees: list EType) (carry: Unification): option Unification :=
    fold_unify (fun inner '(target, assignee) => unify target assignee inner) (combine targets assignees) carry.

(* ---------------------------------------------------------------------------------------------- *)
(* The unify implementations of the subclasses of BoundTypeReference                              *)
(* `unify` is the recursive call; `self` is the target                                             *)
(* ---------------------------------------------------------------------------------------------- *)

(* RootResolvedTypeReference.unify *)
Definition unify_root_resolved (unify: UnifyFn) (self: EType) (base_type: Class) (arguments: list EType) (assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    | RootResolved _ assignee_base_type assignee_arguments =>
        if negb (base_type_is_subtype_of assignee_base_type base_type) then Some (fail carry) else
        if negb (Model.is_subtype_of (mutability_of assignee) (mutability_of self)) then Some (fail carry) else
        (* Nothing is a subtype of every other possible type, which cannot be denoted in source code *)
        if class_eqb assignee_base_type nothing then Some carry else
        let normalized_assignee_arguments :=
            if class_eqb assignee_base_type base_type
            then assignee_arguments
            else parameterized_supertype_arguments assignee_base_type assignee_arguments base_type in
        unify_arguments unify arguments normalized_assignee_arguments carry
    | Error m _ => unify self (as_nothing (or_readonly m)) carry
    | Generic (mkGenericRef _ _ bound) => unify self bound carry
    | TypeArgument _ type => unify self type carry
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    (* a possibly null value to a non-null reference *)
    | Nullable _ => Some (fail carry)
    | Intersection components => intersection_flipped_unify unify self components carry
    end.

(* NullableTypeReference.unify *)
Definition unify_nullable (unify: UnifyFn) (self nested assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    | Nullable assignee_nested => unify nested assignee_nested carry
    | TypeArgument _ type => unify self type carry
    | Generic (mkGenericRef _ _ bound) =>
        match nested with
        | Generic _ | TypeArgument _ _ => unify nested assignee carry
        | _ => unify self bound carry
        end
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    | _ => unify nested assignee carry
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
Definition unify_generic (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    (* a possibly null value to a non-nullable reference *)
    | Nullable _ => Some (fail carry)
    | Error m _ => unify self (as_nothing (or_readonly m)) carry
    | RootResolved _ _ _ =>
        if is_non_nullable_nothing assignee then Some carry else Some (fail carry)
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    | TypeArgument variance type =>
        match variance with
        | output | invariant => unify self type carry
        | input => unify self top_type carry
        end
    | Generic _ =>
        if generic_is_subtype_of assignee parameter (mutability_of self) then Some carry else Some (fail carry)
    | Intersection components => intersection_flipped_unify unify self components carry
    end.

(* ErroneousType.unify: acts like Any *)
Definition unify_erroneous (unify: UnifyFn) (self: EType) (m: Mutability) (assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    | _ => unify (as_any m) assignee carry
    end.

(* BoundTypeArgument.unify *)
Definition unify_type_argument (unify: UnifyFn) (self: EType) (variance: Variance) (type assignee: EType) (carry: Unification): option Unification :=
    let assignee_is_type_argument := match assignee with TypeArgument _ _ => true | _ => false end in
    (* nothing but Nothing can be assigned to a reference of an out-variant type *)
    if negb assignee_is_type_argument && Variance_beq variance output then
        if is_non_nullable_nothing assignee then Some carry else Some (fail carry)
    else
    match assignee with
    | RootResolved _ _ _
    | Nullable _ => unify type assignee carry
    | TypeArgument assignee_variance assignee_type =>
        match variance, assignee_variance with
        (* the target uses the type both in IN and OUT fashion, the source must match exactly *)
        | invariant, invariant =>
            let* carry2 := unify type assignee_type carry in
            unify assignee_type type carry2
        | invariant, _ => Some (fail carry)
        | output, output
        | output, invariant => unify type assignee_type carry
        | output, input => Some (fail carry)
        (* IN variance reverses the hierarchy direction *)
        | input, input
        | input, invariant => unify assignee_type type carry
        | input, output => Some (fail carry)
        end
    | Generic _ => unify type assignee carry
    | Intersection components => intersection_flipped_unify unify self components carry
    | Error m _ => unify self (as_nothing (or_readonly m)) carry
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    end.

(* TypeVariable.unify *)
Definition unify_type_variable (unify: UnifyFn) (self: EType) (parameter: TypeParameterId) (assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    | RootResolved _ _ _
    | Generic _
    | Intersection _
    | TypeArgument _ _ => plus_supertype_constraint unify carry parameter assignee
    | Error m _ => unify self (as_nothing (or_readonly m)) carry
    (* Kotlin throws an InternalCompilerError *)
    | TypeVariable _ => None
    | Nullable nested =>
        if is_nullable self then plus_supertype_constraint unify carry parameter assignee else
        (* A possibly null value to a non-nullable reference. Kotlin carries on unifying without
           the null, for the sake of more diagnostics; it fails either way. *)
        Some (fail carry)
    end.

(*
 * BoundIntersectionTypeReference.unify. Types are seen as the promises a value makes to its users:
 * before unifying the type variables among the components, the promises already covered by the
 * other components are subtracted from the assignee, so as not to force the variables into a
 * needlessly narrow corner.
 *)
Definition unify_intersection (unify: UnifyFn) (self: EType) (components: list EType) (assignee: EType) (carry: Unification): option Unification :=
    match assignee with
    | Nullable nested =>
        (* a possibly null value to a non-null reference *)
        if negb (is_nullable self) then Some (fail carry) else unify self nested carry
    | TypeVariable (mkGenericRef _ p _) => type_variable_flipped_unify unify self p carry
    | Error m _ => unify self (as_nothing (or_readonly m)) carry
    | _ =>
        let var_components := filter is_type_variable components in
        let non_var_components := filter (fun c => negb (is_type_variable c)) components in
        let* carry2 := fold_unify (fun inner component => unify component assignee inner) non_var_components carry in
        let* covering := find_first (fun component => unify component assignee carry2) non_var_components in
        let '(new_assignee, carry3) :=
            match covering with
            | None => (assignee, carry2)
            | Some (covering, carry3) =>
                let covered_any := RootResolved
                    (Some (intersect_mutability (mutability_of assignee) (mutability_of covering)))
                    any [] in
                let new_assignee :=
                    if negb (is_nullable covering) && is_nullable assignee
                    then Nullable covered_any
                    else covered_any in
                (new_assignee, carry3)
            end in
        fold_unify (fun inner component => unify component new_assignee inner) var_components carry3
    end.

(* BoundTypeReference.unify, dispatching on the class of the target *)
Definition unify_step (unify: UnifyFn) (target assignee: EType) (carry: Unification): option Unification :=
    match target with
    | RootResolved _ base_type arguments => unify_root_resolved unify target base_type arguments assignee carry
    | Nullable nested => unify_nullable unify target nested assignee carry
    | Generic (mkGenericRef _ parameter _) => unify_generic unify target parameter assignee carry
    | Error m _ => unify_erroneous unify target (or_readonly m) assignee carry
    | TypeArgument variance type => unify_type_argument unify target variance type assignee carry
    | TypeVariable (mkGenericRef _ parameter _) => unify_type_variable unify target parameter assignee carry
    | Intersection components => unify_intersection unify target components assignee carry
    end.

(*
 * Once a unification has failed, it stays failed; nothing that follows changes the outcome. So
 * unify stops there, where Kotlin carries on collecting diagnostics.
 *)
Fixpoint unify (fuel: nat) (target assignee: EType) (carry: Unification): option Unification :=
    if failed carry then Some carry else
    match fuel with
    | O => None
    | S fuel' => unify_step (unify fuel') target assignee carry
    end.

(* BoundTypeReference.isAssignableTo: whether a value of type `sub` can be assigned to a reference
   of type `super`, i.e. whether `sub` is a subtype of `super`. None if unify gives no answer. *)
Definition is_assignable_to (fuel: nat) (sub super: EType): option bool :=
    option_map (fun u => negb (failed u)) (unify fuel super sub empty_unification).

Lemma unify_keeps_failure: forall fuel target assignee carry,
    failed carry = true -> unify fuel target assignee carry = Some carry.
Proof. intros [|fuel] target assignee carry H; simpl; rewrite H; reflexivity. Qed.

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
    intros fuel m c. unfold is_assignable_to. simpl. unfold unify_root_resolved.
    unfold base_type_is_subtype_of. rewrite class_eqb_refl, mutability_is_subtype_of_refl. simpl.
    destruct (class_eqb c nothing); reflexivity.
Qed.

(* exclusive Nothing is a subtype of every non-nullable class type. *)
Theorem bottom_type_is_assignable_to_root_resolved: forall fuel m c arguments,
    is_core_scalar (declaration_of nothing) = false ->
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

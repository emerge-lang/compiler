# Proof coverage

What the proofs in [`theories/`](theories) cover of the type system, and what they don't. The premises
the proofs take are listed once, in the [readme](readme.md#what-the-proofs-assume); this file only
refers to them. Keep it up to date with every change to the proofs or to the type system.

✓ proven · ◐ proven in a weaker form, or under a conjecture · ✗ not covered

## Surprising blind spots

| # | what isn't covered | example | why |
|---|---|---|---|
| 4 | A bound mentioning another variable, with no argument giving that variable a lower bound, but in calls from generic code and instantiated, where the bound mentions only type parameters of the function and is a class type or a type variable | `fn f<A, B : List<A>>(a: A) -> B` from a free or member function's caller; `T : A & U`, `T : U?`, `fn m<T : List<E>>` with `E` of the class; on generic receivers | Kotlin's final value of such a variable is its upper bound intersected with the bound, its type variables replaced by their final values, as a value of it reads (`Constraints.final_value_with`; an F-bounded one without a lower bound is an error). `GenericArguments.generic_member_call_with_bounded_variables_sound` and `GenericCode.generic_member_call_with_bounded_variables_instantiated` take the final values so (`unbounded_shape`), which covers non-generic code too (no type parameters of the caller). Not covered: the free and member function columns, whose theorems (`FBounded`) don't take intersections as final values; generic receivers (`GenericReceivers`); intersections as the bound, whose instances may keep their nullability (#15, step 12); `U?`; and bounds mentioning a type parameter of the class. Of one captured from a variant receiver, the value isn't within the bound for the object (`T : E` on a `Mk<out A>` holding a `Mk<C>` is `A`), and of an `in` capture it may be nullable where the bound isn't: no value of such a variable reaches the function, but the invariants the proofs keep (`nonnull_values`, the final values within their bounds) don't hold of it |
| 5 | Explicit type arguments for a function whose bounds mention type variables, but those of a free function, of class types | `box.m::<Num>()` with `fn m<T : Ord<in E>>` in `class Box<E>`; `make::<T>()` in generic code | `Explicit.explicit_invocation_with_bounded_variables_sound` covers free functions, binding the type parameters in the order they are declared, each type argument checked against its bound with those declared before bound already (`Subtyping.bind_explicit`, Kotlin's `fromExplicit`). Kotlin binds the explicit type arguments of a member function before it captures the type arguments of the receiver, so a bound mentioning a type parameter of the class is checked while that may still be captured, by the check; probes of that found nothing unsound. Neither that order nor explicit type arguments mentioning type parameters of the caller are modelled |
| 10 | Bounds that are neither class types nor types of the parameters, or with type variables in type arguments of a mutability given to them or narrowed, and parameter types with such type arguments or that are intersections, where the final values aren't class types, outside of generic code (◐‡) | `T : A & B` or `T : A & Ord<in T>` inferred to an intersection, `T : U?` or `T : U!` to a type parameter, `B : List<mut A>`, `x: Box<A!>` or `x: A & B` with `A` inferred to an intersection, in non-generic code | Premise of FBounded and MemberCalls (of type arguments, where they aren't plain, `args_plain`; of intersections as parameter types, `inter_of`): with it, every reference to a type parameter, of any mutability and `!`, is within its bound as those of a caller are (`WithinBounds.param_refs`), and an intersection of class types is below the instance of its components (`below_intersection_instance`), which take class-type bindings; non-generic code is covered only as generic code without type parameters of the caller, under its conjectures |
| 11 | Member access in generic code where the instances aren't class types, or of members typed as intersections; overrides of intersection types | `box.value` with `box: Box<A & T>`; `b.v` with `b: H<T>` and `v: A & X`; an override taking `A & T` | `Composition.v` covers reads and writes through a reference mentioning type parameters, and through a value of a type parameter, which the frontend reads as its bound (roadmap 32): instantiated for the run-time bindings, they are those through the reference at run time (`compose_member`, for member types as MemberAccess has them). At run time, MemberAccess takes over, which needs the instances of the type arguments of the reference, and of a value written, to be class types. Intersections as member types are left out, also those whose components keep their nullability, `A? & T`, which are types of generic code since step 12. The frontend agrees over the grid (`MemberAccessPropertiesTests`) |
| 13 | In generic code, types that are Nothing without being `Nothing` among the types of the arguments: intersections with a Nothing component or of disjoint classes, type parameters bounded by Nothing | `x: mut A & read Nothing` (the frontend makes it `const A & Nothing`), `n: N` with `N : Nothing` | Unify takes them for Nothing (`is_non_nullable_nothing`): an `out` type argument takes them, and a variable with one as its lower bound falls back to its upper bound. The proofs show of `Nothing` itself only that what unify takes for Nothing is below every type (`bottom_only_nothing`, `below_nothing`); `bottom_only` keeps the others out. No value has such a type; the frontend warns of `mut A & read Nothing`. `Nothing` itself, of any mutability, is covered (roadmap 35, step 10) |
| 15 | Intersections whose components keep their nullability, with type variables among them, as the types of parameters of calls in generic code, instantiated, or of functions whose bounds mention type variables | `fn id<P>(x: A? & P) -> A? & P`, `id(null)` in a generic function, its body instantiated | ofComponents makes `(A & B)?` only where every component is `X?`, non-null components where one isn't nullable, and otherwise keeps the components as they are, so that null is a value exactly where it is one of each component: `A? & P`, `P & R` with `P, R : Any?`. They are covered as the types of arguments and final values (`gfrag`: unify with them is transitive, `Generics.transitivity_never_fails`, and `intersect` builds them, `intersect_always_stays_in_fragment`) and as the types of generic code (`GenericCode.caller_type`, of `SubstitutionWide.ktfrag`, also in type arguments and made nullable: the substitution lemma holds of them, `substitution_wide`, and `intersect` builds them, `intersect_stays_in_generic_code`); `OracleGrid.v` checks both conjectures of the frontend over `TypeGrid` (step 12, step 16). As the types of parameters, outside generic code (`Inference.kqfrag`: of an argument that may be null, which a component covers, the variables take `Any?`, `Constraints.param_components`; the instance, `ofComponents` of class types, nullable or not, takes what the instance of each component takes, `Inference.below_flat_components`), and in generic code (`GenericArguments.member_call_in_generic_code_sound`: `gparam_components`, and `below_of_components_nullable` of an argument that may be null). Not yet instantiated (`GenericCode`, `GenericReceivers`; the model's `(A? & P)?` for `T?` of `T` bound to `A? & P`, where the frontend makes `(A & P!)?`, is in the way, step 12), nor with bounds that mention type variables (`GenericArguments.mqparameter`), which take `qfrag`, of intersections of non-null components only. Inferring from an argument that may be null, the frontend and the model took null as covered by the component that takes the argument, and bound `P` to a non-null `Any`: `id(null)` was an `A`. Both now leave null to every component (`Subtyping.intersection_body`) |
| 16 | Programs on which the model's unify doesn't terminate, wherever the theorems rest on `unify_terminates_on` (◐) | `fn f<T : Cn<Cn<in T>>>(t: T) { val c: Cn<in T> = t }`; `class K : Cn<Cn<in K>>` | Deciding `T` below `Cn<in T>` unfolds the bound to `Cn<Cn<in T>>`, and the in-variant type argument swaps target and assignee: the question comes up again, and the model's unify gives no answer with any fuel (`Examples.Counterexample`); the same through supertypes (Kennedy and Pierce's example). The frontend fails such a goal (`RootResolvedTypeReference.unify`, `UnificationPropertiesTests`); the model doesn't. The claim that unify terminates wherever inheritance is tame (`unify_always_terminates`) is refuted (`Examples.unify_always_terminates_is_false`): F-bounds bring the contravariance in without inheritance. So the theorems of generic code take termination on the program at hand as a premise (`Conjectures.unify_terminates_on`), like the conjectures about `intersect` and `closestCommonSupertypeWith`; which programs satisfy it is open, plausibly those without `in` type arguments anywhere, and modelling the frontend's cut is roadmap item 39 |
| 17 | Calls outside generic code to a function whose bounds mention other type parameters, with an argument or explicit type argument that has an in-variant type argument, nested ones included; and such calls in programs with a supertype declaration that has one nested (✗) | `fn f<T, U : Box<T>>(a: T, u: U)`, `f(x, u)` with `x: Box<in A>`; `class H<T> : Base<Consumer<in T>>` anywhere in the program | The join of two class types with in-variant type arguments intersects them: `Box<in A> ⊔ Box<in B> = Box<in A & B>`, precise and sound, but no class type (`Inference.afrag`), which the check of a lower bound against a static upper bound with type variables takes (`Constraints.static_whole`); found by `CommonTypesTests` over the widened grid (step 14). `closest_common_supertype_of_classes` is narrowed to class types without contravariance (`Inference.without_contravariance`), whose join is one, without it, as `OracleGrid.v` checks over `TypeGrid` (step 15, step 16). The variable states have static upper bounds with type variables only where the arguments are without contravariance (`Constraints.strict`), so the theorems take that only of calls to functions with such bounds (`Constraints.arguments_without_contravariance`: `FBounded.v`, `Explicit.v`); calls to others take any class-type arguments (`fn f<T>(x: Box<in T>)`, `MemberCalls.v`, `FinalValues.v`). Normalizing an argument to a supertype keeps it without contravariance where the supertype declarations have no nested `in` (`Inference.supertypes_without_contravariance`, part of `arguments_without_contravariance`, so taken of such calls only; immediate type arguments of supertypes have no variance, `wf_supertypes_are_exact`). The same calls in generic code are covered by `GenericArguments.v`, whose fragment admits intersections in in-variant type arguments, under its premises; outside generic code, covering them takes widening the inference proofs to those intersections |
| 18 | Calls in generic code with an argument `Box<in Nothing?>` or `Box<Nothing?>` against another whose type argument is a type parameter (◐) | `fn f<T>(a: T, b: T)`, `f(Box<P>, Box<in Nothing?>)` in generic code | The join is `Box<in P & Nothing?>`: the intersection is Nothing without null, which `GenericArguments.bottom_only` excludes, so `closest_common_supertype_keeps_bottom_only` is false of the frontend (step 14). The theorems of generic code taking it say nothing about the frontend until `bottom_only` admits such intersections, which rests on unify treating an intersection that is Nothing as Nothing (the frontend does since step 14, the model doesn't yet). `OracleGrid.v` excuses the 38 pairs of `TypeGrid` it fails on, and only those: where the join, but for its intersections as in-variant type arguments, is `bottom_only` |

## Subtyping (unify)

| area | status | where |
|---|---|---|
| Class types (variance, ownership, nullability): transitivity, reflexivity | ✓ | `Transitivity.v` |
| Mutability promises are conflict-free; assignability respects mutability | ✓ | `Ops.v` |
| Const classes (fit every mutability) | ✓ | `Subtyping.v`, `Ops.v` |
| Type parameters, `m T`, `T!`, `T?`, intersections: transitivity | ◐ proven only to never reject; accepting rests on `unify_terminates_on` | `Generics.v`, `Conjectures.v` |
| Reflexivity on type parameters and intersections | ◐ same | `FinalValues.v` |
| Erroneous types | ✗ modelled in unify, no theorem | — |
| The frontend's unify is the model's, over the types of `TypeGrid` | ✓ by computation, but intersections of disjoint classes, which the frontend takes below every type (step 14) | `OracleGrid.unify_agrees` |
| Ownership (`owned`/`ref`) | ✓ but not implemented in Kotlin | `Ownership.v` |

## Substitution (instantiating type parameters)

| area | status | where |
|---|---|---|
| Class types, `T`, `m T`, `T!`, `T?`, bounds mentioning other parameters, F-bounds | ✓ | `Substitution.v` |
| Intersections at the top level and as assignees | ◐ assumes `unify_terminates_on` | `SubstitutionTerminating.v` |
| Intersections inside type arguments (`Box<A & T>`) | ◐ assumes `unify_terminates_on` | `SubstitutionWide.v` |
| Explicit type arguments within declared bounds, including F-bounds | ✓ | `WithinBounds.v` |

## Member access

| area | status |
|---|---|
| Read and write through variant type arguments; members typed `T`, `T?`, `m T`, `T!`, `m T?`, class types of those; explicit ownership | ✓ `MemberAccess.v` |
| Member types that are intersections of those, made nullable or not (`A & T`, `(A & T!)?`, `A? & T`), but of components `T?` | ◐ `MemberIntersections.v` (assumes `unify_terminates_on`) |
| In generic code and through values of type parameters, for the member types of `MemberAccess.v`: what is read and written, instantiated, is so through the reference at run time | ◐ `Composition.v`: `generic_member_read_sound`, `generic_member_write_sound` (assumes `unify_terminates_on`; run-time type arguments class types, #11) |
| Members typed as intersections in generic code | ✗ (#11) |
| Objects of a subclass of the reference's class | — only classes have member variables, and classes have no subtypes (`BoundBaseType.Kind`) |

## Calls and inference, by the callee's bound shape

Columns:

- **free fn**: a function without a receiver, called with class-type arguments.
- **member fn**: called on a receiver of class type, including subclasses, with class-type arguments. The type
  parameters of the class may be bounded as those of the function (`class Node<T : Ord<in T>>`,
  `class Wrap<A, B : Holder<A>>`), in the cells with \*, declared in order and before those of the function, as
  Kotlin has them, with the type arguments of the object within the bounds, instantiated; where such a bound is
  neither a class type nor a type of the parameters, † applies.
- **from generic code**: arguments mention the caller's type parameters, or are intersections; ‡ with parameter types
  without ownerships of type parameters (which Kotlin doesn't have).
- **instantiated**: generic code with its type parameters bound at run time.
- **generic receiver**: `list.add(x)` with `list: List<T>`.

| callee's type-parameter bound | free fn | member fn | from generic code | instantiated | generic receiver |
|---|---|---|---|---|---|
| class type (`Foo`, `Any?`, `Box<X>`) | ✓ | ✓ | ◐ | ◐ | ◐ |
| closed intersection (`A & B`, `(A & B)?`) | ✓† | ✓† | ◐‡ | ◐‡ | ◐‡ |
| another parameter (`T : U`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| a type parameter of the class (`T : E`, `T : Ord<in E>`) | — | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter, nullable (`T : U?`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter (`B : List<A>`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter made nullable in type arguments (`B : List<A?>`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter narrowed in type arguments (`B : List<A!>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter of a given mutability in type arguments (`B : List<mut A>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| F-bound (`T : Ord<in T>`, `T : Ord<in T>?`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| intersection with variables (`T : A & Ord<in T>`, `T : A & U`, a component `m U` or `U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| nullable intersection with variables (`T : A? & Ord<in T>?`, `T : A? & U?`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter, narrowed (`T : U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter of a given mutability (`T : mut U`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |

\* only when every such variable gets a lower bound from the arguments, and only for inference, but explicit
type arguments of class types for free functions (#5); in the from-generic-code and instantiated columns, a variable without one where its bound
mentions only type parameters of the function and is a class type or a type variable (#4). In the free and member function
columns, only for arguments and explicit type arguments without in-variant type arguments, nested ones included, in programs
whose supertype declarations have none nested (#17).
† only when the final values are class types.
◐ assumes the conjectures about `intersect` and `closestCommonSupertypeWith`, of which `OracleGrid.v` finds
`closest_common_supertype_keeps_bottom_only` false of the frontend (#18), and `unify_terminates_on` (#16); in generic code
also that the types of the arguments are Nothing only as `Nothing` (#13), and none of the callee's type
parameters as an ownership. Of an intersection bound, the final value is shown within each component (`bound_components`).

Of parameter types, type variables in type arguments are covered in the cells above: made nullable (`Box<T?>`)
in every column, of non-null bounds too; of a given mutability or narrowed (`Box<mut T>`, `Box<T!>`) with † for
free and member functions, and in generic code. So are intersections, nullable or not (`x: T & A`, `x: T? & A?`),
with † for free and member functions, and in generic code: the argument is below the instance of the whole
intersection, as ofComponents makes it.

Within the covered cells, these are proven: explicit type arguments and receiver capture (`Inference.v`),
lower and upper bounds and the final values chosen (`Constraints.v`), receivers of subclasses with exact
supertype arguments (`MemberCalls.v`), receivers of classes whose type parameters are bounded by types mentioning
them, captured in the order they are declared, each bound checked with the type parameters it mentions bound
already (`MemberCalls.receiver_captures_ranked`), and their values not nullable where their bounds aren't
(`GenericArguments.values_not_nullable_among`), final values that are type parameters or intersections
(`FinalValues.v`), bounds with type variables, for free and member functions (`FBounded.v`:
`invocation_with_bounded_variables_sound`, `member_call_with_bounded_variables_sound`), and in generic code
(`GenericArguments.v`: `generic_invocation_with_bounded_variables_sound`,
`generic_member_call_with_bounded_variables_sound`; instantiated, `GenericCode.v`:
`generic_member_call_with_bounded_variables_instantiated`; on receivers of generic code, at run time,
`GenericReceivers.v`: `generic_receiver_with_bounded_variables_sound`). Calls from generic code take arguments of any type of
the fragment, intersections among them; non-generic code is the case without type parameters of the caller (`ps = []`
in `GenericCode.v`), so they cover what the class-type-argument columns leave out, under the conditions of ◐.

## Overrides (dynamic dispatch)

| area | status | where |
|---|---|---|
| An argument the call takes fits the override's parameter, with the type parameters of the object's class bound | ✓ | `Overrides.v`: `override_parameter` |
| What the override returns fits the return type the call expects | ✓ where the object's type arguments are within their bounds | `override_return` |
| The object fits the override's declared receiver (an override can't demand `mut` where the overridden function takes `read`) | ✓ class-type receivers; the intersection Kotlin checks is taken unsimplified | `override_receiver` |
| Parameter and return types `m T`, `T!`, `T?`, class types of those | ◐ assumes `unify_terminates_on` | `Composition.v`: `override_parameter_composed`, `override_return_composed` |
| Parameter and return types that are intersections | ✗ (#11) | — |
| Functions with type parameters of their own | — Kotlin can't override them (roadmap 34) | — |
| Every function a concrete class inherits is implemented, so dispatch finds one | assumed: the compiler reports `AbstractInheritedFunctionNotImplementedDiagnostic` otherwise (`PossiblyMixedInBoundMemberFunction`) | readme, assumptions |

## Outside the proven model entirely

* Overload resolution
* Casts and instance-of checks (`as`, `is`): out of scope until there is runtime reflection on type argument
* Constructors and object initialization (`PartialObjectInitialization`), mixins: these are simple enough that proving
  them formally seems not worthwhile at the moment
* Lifetimes and exclusive-reference tracking (`VariableLifetime`); `Ops.v` covers the static promises of references only.
* Declaration-site variance, which emerge doesn't have yet
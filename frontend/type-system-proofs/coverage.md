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
| 15 | Intersections whose components keep their nullability, with type variables among them, as the types of parameters of calls in generic code, instantiated, or of functions whose bounds mention type variables | `fn id<P>(x: A? & P) -> A? & P`, `id(null)` in a generic function, its body instantiated | ofComponents makes `(A & B)?` only where every component is `X?`, non-null components where one isn't nullable, and otherwise keeps the components as they are, so that null is a value exactly where it is one of each component: `A? & P`, `P & R` with `P, R : Any?`. They are covered as the types of arguments and final values (`gfrag`: unify with them is transitive, `Generics.transitivity_never_fails`, and `intersect` builds them, `intersect_always_stays_in_fragment`) and as the types of generic code (`GenericCode.caller_type`, of `SubstitutionWide.ktfrag`, also in type arguments and made nullable: the substitution lemma holds of them, `substitution_wide`, and `intersect` builds them, `intersect_stays_in_generic_code`); `CommonTypesTests` checks both conjectures of the frontend (step 12). As the types of parameters, outside generic code (`Inference.kqfrag`: of an argument that may be null, which a component covers, the variables take `Any?`, `Constraints.param_components`; the instance, `ofComponents` of class types, nullable or not, takes what the instance of each component takes, `Inference.below_flat_components`), and in generic code (`GenericArguments.member_call_in_generic_code_sound`: `gparam_components`, and `below_of_components_nullable` of an argument that may be null). Not yet instantiated (`GenericCode`, `GenericReceivers`; the model's `(A? & P)?` for `T?` of `T` bound to `A? & P`, where the frontend makes `(A & P!)?`, is in the way, step 12), nor with bounds that mention type variables (`GenericArguments.mqparameter`), which take `qfrag`, of intersections of non-null components only. Inferring from an argument that may be null, the frontend and the model took null as covered by the component that takes the argument, and bound `P` to a non-null `Any`: `id(null)` was an `A`. Both now leave null to every component (`Subtyping.intersection_body`) |
| 16 | Programs on which the model's unify doesn't terminate, wherever the theorems rest on `unify_terminates_on` (◐) | `fn f<T : Cn<Cn<in T>>>(t: T) { val c: Cn<in T> = t }`; `class K : Cn<Cn<in K>>` | Deciding `T` below `Cn<in T>` unfolds the bound to `Cn<Cn<in T>>`, and the in-variant type argument swaps target and assignee: the question comes up again, and the model's unify gives no answer with any fuel (`Examples.Counterexample`); the same through supertypes (Kennedy and Pierce's example). The frontend fails such a goal (`RootResolvedTypeReference.unify`, `UnificationPropertiesTests`); the model doesn't. The claim that unify terminates wherever inheritance is tame (`unify_always_terminates`) is refuted (`Examples.unify_always_terminates_is_false`): F-bounds bring the contravariance in without inheritance. So the theorems of generic code take termination on the program at hand as a premise (`Conjectures.unify_terminates_on`), like the conjectures about `intersect` and `closestCommonSupertypeWith`; which programs satisfy it is open, plausibly those without `in` type arguments anywhere, and modelling the frontend's cut is roadmap item 39 |
| 17 | Calls with arguments whose in-variant type arguments differ, where the callee's bounds mention other type parameters, outside generic code: the ✓ theorems of inference take `closest_common_supertype_of_classes`, which is false of the frontend (◐‡) | `fn f<T, U : Box<T>>(a: T, b: T, u: U)`, `f(box1, box2, u)` with `box1: Box<in A>`, `box2: Box<in B>` | The join of two class types with in-variant type arguments intersects them: `Box<in A> ⊔ Box<in B> = Box<in A & B>`, precise and sound, but no longer a class type (`Inference.afrag`), which the check of the lower bound against a static upper bound with type variables takes (`Constraints.static_whole`); found by `CommonTypesTests` over the widened grid (step 14). As a claim about the frontend, the premise is false, so until it is narrowed to arguments without in-variant type arguments (`Conjectures.without_contravariance`) or the inference proofs admit intersections inside in-variant type arguments, `Constraints.invocation_sound` and what takes it (`Explicit.v`, `FBounded.v`, `MemberCalls.v`, `FinalValues.v`) say nothing about the frontend; the same calls in generic code are covered by `GenericArguments.v`, whose fragment admits such types, under its premises |
| 18 | Calls in generic code with an argument `Box<in Nothing?>` or `Box<Nothing?>` against another whose type argument is a type parameter (◐) | `fn f<T>(a: T, b: T)`, `f(Box<P>, Box<in Nothing?>)` in generic code | The join is `Box<in P & Nothing?>`: the intersection is Nothing without null, which `GenericArguments.bottom_only` excludes, so `closest_common_supertype_keeps_bottom_only` is false of the frontend (step 14). The theorems of generic code taking it say nothing about the frontend until `bottom_only` admits such intersections, which rests on unify treating an intersection that is Nothing as Nothing (the frontend does since step 14, the model doesn't yet) |

## Subtyping (unify)

| area | status | where |
|---|---|---|
| Class types (variance, ownership, nullability): transitivity, reflexivity | ✓ | `Transitivity.v` |
| Mutability promises are conflict-free; assignability respects mutability | ✓ | `Ops.v` |
| Const classes (fit every mutability) | ✓ | `Subtyping.v`, `Ops.v` |
| Type parameters, `m T`, `T!`, `T?`, intersections: transitivity | ◐ proven only to never reject; accepting rests on `unify_terminates_on` | `Generics.v`, `Conjectures.v` |
| Reflexivity on type parameters and intersections | ◐ same | `FinalValues.v` |
| Erroneous types | ✗ modelled in unify, no theorem | — |
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
mentions only type parameters of the function and is a class type or a type variable (#4).
† only when the final values are class types.
◐ assumes the conjectures about `intersect` and `closestCommonSupertypeWith`, and `unify_terminates_on`; in generic code
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

## Outside the model entirely

| area |
|---|
| Overload resolution |
| Casts and instance-of checks (`as`, `is`): out of scope until there is runtime reflection on type arguments (roadmap 13); their type arguments go unchecked until then, by design |
| Constructors and object initialization (`PartialObjectInitialization`), mixins |
| Lifetimes and exclusive-reference tracking (`VariableLifetime`); `Ops.v` covers the static promises of references only. Unsound through type variables: a value of type `T` is copied freely, and an exclusive value passed for a parameter of type `T` keeps its lifetime, `T` inferred as its exclusive type (roadmap 20) |
| Declaration-site variance, which emerge doesn't have |

## Order of work

Towards full coverage, in this order: first what is likeliest to turn up soundness problems, and tests of the
compiler where they narrow a gap for much less than a proof would. The proofs are about the model, which is tied
to the Kotlin code by review only, and every hole found so far was where the two were compared: by modelling
Kotlin code (`V` assignable to `V!`, a nullable value taken for `T!`, type variables losing `!` and their
mutability on instantiation, the closest common supertype of variant type arguments), or by testing Kotlin over a
grid of types (`CommonTypesTests`: `ofComponents` taking `P : Any?` as nullable). So tests come first. Then come
proofs, of what the tests leave most at risk.

Done:

1. ~~Override dispatch~~ (done: `Overrides.v`)
2. ~~Generic code with bounds that mention type variables~~ (done: free and member functions called from generic
   code, their instances, and calls on receivers of generic code, intersection bounds among them;
   `instantiate_free`, `GenericArguments`: `mixed_arguments`, `gstatic_whole`, `gleaf_all`,
   `generic_invocation_with_bounded_variables_sound`, `generic_member_call_with_bounded_variables_sound`;
   `GenericCode.generic_member_call_with_bounded_variables_instantiated`; `GenericReceivers`: `runtime_mixed`,
   `rstatic_whole`, `rleaf_all`, `generic_receiver_with_bounded_variables_sound`. With them arguments that aren't
   class types, formerly #8, and calls on receivers of generic code, formerly #7. Intersections of the fragment are
   uniform, their components assigned as one mutability, as `ofComponents` builds them)
3. ~~The remaining type shapes, in that setting~~, all but #15 (step 7 below; #3 in step 9): of bounds, #1 closed intersections (done, of the bounds of the
   inference interface, as FinalValues has them: `static_bound`, `bindings_within` through `inter_accepts`), #2 nullable intersections (done:
   `inter_of`, `static_components`, `gstatic_components`, `rstatic_components`; of type variables among the components,
   `components_of`, `rewrap_takes`), #3 `T : U?`, #6 `m T` / `T!` (type variables among the components of an
   intersection done, of a mutability given to them or narrowed, as ofComponents gives every component the common
   mutability, `A & U` being `A & read U`, and narrows those of a nullable bound: `Inference.compfrag`,
   `compfrag_given`, `static_component_cases`, `narrowed_component`, `narrowed_variable_not_nullable`,
   `free_variable_any`; as the whole bound done, `T : U?`, `T : U!`, `T : m U`, `T : m U?`, in every setting: `Constraints.reference_step`, `static_whole`; `FBounded.bindings_within` through
   `WithinBounds.param_refs`, `mentions_of_static`; `gstatic_whole` through `mixed_parameter`;
   `rstatic_whole` through `runtime_mparameter`); of parameter types, #12 (a type variable as the whole type of a parameter done,
   `T?`, `T!`, `m T`, `m T?`, in every setting: `pfrag`, `pgeneric`,
   `unify_variable_given`, `Generics.target_ordered`, `instance_never_fails`, `parameter_step`,
   `exact_parameter`, `generic_parameter`, `mixed_parameter`, `runtime_parameter`, `runtime_mparameter`; type
   variables in type arguments of parameter types done, `Box<T?>`, `Box<T!>`, `Box<m T>`, in every setting: `nfrag`,
   `Inference.reference_target`, `reference_assignee`, `Constraints.nested_target_step`, `nested_assignee_step`,
   `Generics.instance_within_never_fails`, `MemberCalls.refs_fuel`, `FBounded.args_plain_candidate`,
   `GenericArguments.gnested_target`, `mnested_target`, `GenericReceivers.rnested_target`, `rmnested_target`; with
   them, of bounds outside of generic code, `B : List<A?>`, `B : List<m A>`, `B : List<A!>`; in bounds in generic
   code done, the bounded variable itself among them (#3, step 9): `GenericArguments.bplain`,
   `mfrag_candidate`, `FreeInstances.plain_variables`, `other_ref_bound`, `self_ref_value`; `m T`
   instantiated and on generic receivers done, as the whole type and in type arguments, of parameters and bounds:
   `GenericCode.tfrag_given`, `wtfrag_given`, `caller_ref_apply`; `GenericReceivers.ground_given_target`,
   `runtime_mutability`, `instance_given`, `instance_ref_apply`; intersections as parameter types done: `Inference.qfrag`, `below_intersection_instance`, `Constraints.param_components`, `parameter_step`,
   `MemberCalls.pbound_in_from_refs`, `FBounded.bindings_within`,
   `GenericArguments.below_of_components`, `gparam_components`, `generic_qparameter`, `mparam_components`,
   `mqparameter`, `GenericCode.caller_of_components`, `qinst_caller`, `qfree_caller`,
   `GenericReceivers.rparam_components`, `runtime_qparameter`. The model follows ofComponents in keeping the nullability of components that may be null only as their instance may (#15), with instantiated generic code taking the values of type parameters of non-null bounds to be non-null, as they are within their declared bounds: `GenericCode.values_not_nullable`, from the bounds of the type parameters of the callee being the declared ones and, in `generic_member_call_with_bounded_variables_instantiated`, the type arguments of the object within them, as `member_call_in_generic_code_instantiated` already took them. With explicit type arguments, intersections as parameter types done: `Inference.exact_components`, `exact_qparameter`, as `member_call_sound` has them. Whatever the final values, intersections as parameter types done: `GenericArguments.member_call_with_any_final_values_and_intersections_sound`; on generic receivers where the function's bounds mention type variables done: `GenericReceivers.rmparam_components`, `runtime_mqparameter`, and at run time, below the instance of each component, below that of the intersection ofComponents makes of them (`runtime_of_components`). `T?` of a non-null bound in type arguments there and in bounds done: a lower bound checked against a non-null static upper bound isn't nullable, as unify took it (`GenericArguments.gstatic_checked`, `gstatic_whole`, `variable_takes_not_nullable`), so neither are the final values of non-null bounds (`gfinal_not_nullable`), and the checks hold for bindings of such values (`nonnull_values`); on generic receivers, with the type arguments of the object within the bounds of the class)
Tests, of the Kotlin code:

4. ~~The conjectures over more types~~ (done: `CommonTypesTests` checks every conjecture about `intersect` and
   `closestCommonSupertypeWith`, over a grid with type-variable components of a given mutability or narrowed,
   three components, `Box<T?>`, F-bounded parameters and #15's `A? & P`, the fragments mirrored in
   `fragments.kt`. Found: the intersection of disjoint classes was `m Nothing` of the components' mutability,
   which generic code admits only as `exclusive Nothing`, now that, the bottom type; and `intersect` makes #15's types of types of
   the fragment, so #15 comes first of the proofs)
5. ~~Kotlin's unify, for what the proofs show of the model's~~ (done: `UnificationPropertiesTests`, over the grid
   of `CommonTypesTests`, now `TypeGrid`: reflexivity, transitivity, and that bindings within the bounds keep
   assignability when instantiated, all of which hold; and that unify finishes, on class tables with F-bounds and
   recursion through type arguments. It didn't on Kennedy and Pierce's example, `class K : Cn<Cn<in K>>`, the
   frontend overflowing its stack: `unify_terminates` was false. The frontend now fails a goal that comes up again
   while it is decided, and the conjecture takes supertypes without contravariance (#16))
6. ~~End-to-end probes of the blind spots and of what is outside the model~~ (done: some 250 programs, each
   putting a value where its type says it can't be, of #15, #11, members typed `m T`, `T!`, `A & T`, overrides,
   #9, #4, #5, #3, #13, exclusive references and object initialization; regression tests in `TypeErrors`. Found,
   and fixed in the frontend:
   - #15: null as an argument for `A? & P` bound `P` to a non-null `Any`, in the model too
   - #15: `A? & P` with `P` bound to `in A` lost null; such an intersection is now the type argument
   - #11: the members of a value of a type parameter were read and written as the bound of their type, any
     value written (roadmap 32)
   - two crashes: inferring from `Box<A?>` for `Box<A? & P>` (an intersection made non-null with a type
     variable among the components), and an intersection in the type arguments of a supertype (roadmap 38,
     outside the type system, open)

   And outside the model, open: exclusive values through type variables (roadmap 20). Overrides, receivers,
   explicit type arguments, variables without a lower bound, `T : Ord<in T?>`, `read Nothing` and object
   initialization held. Steps 8 and 12 prove what was fixed)

Proofs:

7. ~~#15, so that the theorems apply to the compiler~~ (done, for non-generic code: `intersect_stays_in_fragment`
   is claimed only of operands that don't keep their nullability, which `CommonTypesTests` checks, and the bounds
   of non-generic code never do, with `intersect_makes_no_bare_nullable` and
   `closest_common_supertype_makes_no_bare_nullable`: `FinalValues.bound_fragment`. Widening gfrag to the
   intersections themselves, which generic code needs, touches some ninety places where the proofs take
   intersections of the fragment to be non-null, the transitivity proof among them: step 12)
8. ~~#11 member access~~ (done, but intersections in generic code: of members typed `m T`, `T!`
   (`MemberAccess.inst_ref_mono`) and intersections (`MemberIntersections.v`, the model lifting the variance as
   the frontend does, `Subtyping.intersect_instances`); in generic code and through values of type parameters,
   and overrides of those types (`Composition.v`: instantiating twice is instantiating once with the bindings
   instantiated, `compose_member`, which `MemberAccessPropertiesTests` also checks of the frontend). Found, and
   fixed in the frontend: written through a variantly bound type argument, a member typed as an intersection
   nullable only as its components are took null, `Box<P>? & Q` with `Q` bound to `out B?`, where the object
   may hold a `Box<A> & B`; `instantiateAllParametersForWriting` now leaves null to members declared `X?`, as
   the model has it)
9. Inference variants and receivers, then the bounded variable itself: ~~#9 receivers of classes with such
   bounds~~ (done: the receiver captures the type arguments in the order the type parameters are declared, so that
   the variables a bound mentions are bound exactly when a type argument is checked against it, which leaves the
   variable states as they are, `MemberCalls.check_same`, `receiver_captures_ranked`; the theorems with bounds
   mentioning type variables take the class's bounds as the function's, in every column), #4 no lower bound (the
   model has Kotlin's final value, `final_value_with`. Found, and fixed in the frontend: where the bound
   mentions a type parameter of the class captured from a variant receiver, the final value was a type
   argument, `out A` as a whole type, or `CI & out read A`; it is now the type a value of it reads as, as for
   member reads, `BoundTypeReference.asReadType`; proven in generic code and instantiated, where the bound
   mentions only type parameters of the function and is a class type or a type variable, by the ranks of the
   variables: `GenericArguments.unbounded_instance`, `unbounded_not_nullable`, `FreeInstances.free_ext_on`; the
   rest of #4 as its row says), #5 explicit type arguments (done for free functions, with type arguments of
   class types: `Explicit.v`, the type arguments within their bounds from the checks Kotlin makes as it binds
   them, `explicit_arguments`, the checked values as `FBounded.bindings_within` takes lower bounds,
   `checked_value`; the rest as its row says), ~~#3 the bounded variable itself~~ (done: of a mutability given
   to it, narrowed or made nullable in type arguments of its own bound, `T : Ord<in T?>`, `T : Mk<mut T>`,
   `T : Ord<in T!>`, in generic code, instantiated and on generic receivers. With the candidate in its place, it
   is what a reference to the variable makes of the candidate, a type of the arguments:
   `GenericArguments.candidate_self`, `yfrag_ref_apply`, `FreeInstances.self_ref_value`; given a mutability, Nothing
   stays Nothing (`bottom_only_ref_apply`, `Generics.top_kept`); made nullable in a bound that isn't nullable, the
   candidates aren't either (`gstatic_form`, `ifrag_candidate_not_nullable`). Made nullable in type arguments
   of a nullable bound, it is narrowed, as the other type variables are (`args_narrowed`): `T : Ord<in T?>?`
   stays out; tests in `TypeErrors`).
10. ~~#13, together with roadmap 35~~ (done: `Nothing` is declared const, `class Nothing : const Any`, so every
    `m Nothing` is assigned as `exclusive Nothing`, and the fragments admit Nothing of any mutability, in parameter
    types, bounds, the types of arguments and type arguments: `read Nothing`, `List<read Nothing>`. The model
    takes Nothing const (`wf_nothing_is_const`) and has no type parameters (`wf_nothing_has_no_type_parameters`);
    `Transitivity.nothing_below`, `GenericArguments.below_nothing`: Nothing of any mutability is below every
    type. In the frontend, the closest common supertype with Nothing takes the mutability it is assigned with;
    tests in `ResolvedTypeReferenceTest`, `TypeErrors`, `TypeInferenceErrors`, `VarianceErrors`, the grid of
    `CommonTypesTests` with `read Nothing`. What stays out of #13: types that are Nothing without being `Nothing`,
    in generic code).
11. Termination of unify. ~~`unify_terminates`, which turns every ◐ into ✓~~: the conjecture, that unify terminates
    wherever inheritance isn't expansive and supertypes are without contravariance, is false (`Examples.v`, 2026-10-31):
    with `fn f<T : Cn<Cn<in T>>>(t: T)`, deciding `T` below `Cn<in T>` asks itself again, and no inheritance is involved.
    Narrowed (2026-10-31) to a premise about the environment at hand, `unify_terminates_on`, which the ◐ theorems take
    like the conjectures about `intersect` and `closestCommonSupertypeWith`; the refuted claim stays as
    `unify_always_terminates`, for its refutation. Open: which programs satisfy the premise (plausibly those without `in`
    type arguments anywhere; no proof), and modelling the frontend's cut (roadmap 39), which fails a goal that comes up
    again while it is decided, so that the model terminates where the frontend does. The cut touches every use of
    unify, and a cut in one alternative of an intersection lets another succeed, so what the theorems show of unify
    accepting doesn't carry over by itself. Not a soundness problem: where unify doesn't finish, the compiler rejects
    the program.
12. #15 in generic code: ~~gfrag widened to intersections whose components keep their nullability, and the
    theorems on it~~ (done: `Fragment.is_kept_component`, `intersection_gfrag_cases`. A target intersection takes
    no `X?`, as one of its components is a reference as it is (`Generics.inter_takes_no_nullable_any`). Transitivity
    through a type in between that may be null, a reference or such an intersection, to a nullable target goes
    through the components and bounds of that type: removing null from the components of an assignee intersection
    can take more fuel than those took (`accepted_without_null` keeps the fuel only of non-null assignees).
    `GenericArguments.bottom_only` checks intersections without null, as `A? & B? & P` of unrelated A and B is
    Nothing without null; `Conjectures.bare_nullable` counts such intersections, as the closest common supertype
    of `A? & P` and `P!` is `P`. `intersect_always_stays_in_fragment` holds of the frontend over the grid of
    `CommonTypesTests`); ~~the types of generic code with them~~ (done: `SubstitutionWide.ktfrag`, at the top and in
    type arguments, and made nullable, as `rewrap_nullable` makes `T?` of `T` bound to one: `(A? & P)?`, with the
    values of the frontend's `(A & P!)?`. Instantiated, such an intersection is `ofComponents` of class types,
    nullable or not, below each and above what is below each (`of_components_below`,
    `below_of_components_ground`); the substitution lemma takes it as the target through each component, as the
    assignee through one, or without null (`wide_kept_target`, `wide_into_kept`, `kept_without_null`). A
    mutability given to one is given to it without null (`GenericReceivers.instance_given`).
    `intersect_stays_in_generic_code` holds of the frontend over the grid). ~~Such intersections with type
    variables among the components as the types of parameters, outside generic code~~ (done: `Inference.kqfrag`,
    `Constraints.param_components` and `Inference.exact_components` of components `A?` and arguments that may be
    null, `Inference.below_flat_components`; `id(null)` with `fn id<P>(x: A? & P)`, as step 6 found). ~~In generic
    code~~ (done: `GenericArguments.gparam_components` of components `A?` and arguments that may be null,
    `below_of_components_nullable`). Open: those instantiated (`GenericCode`, `GenericReceivers`), and with bounds
    that mention type variables (`GenericArguments.mqparameter`), on `qfrag`. Instantiated, the instance of such a
    parameter type is an intersection of types of generic code, which `T?` of `T` bound to `A? & P` breaks: the
    model's `rewrap_nullable` makes it `(A? & P)?`, whose components `A??` and `P?` are none, where the frontend's
    `NullableTypeReference` makes `(A & P!)?`. Matching the frontend takes `rewrap_nullable` the environment, for
    whether `P` is narrowed, in some 300 places; requiring the final values to be of `gfrag`, which leaves
    `(A? & P)?` out, is the smaller way; members and overrides typed as
    intersections in generic code (#11).
13. Exclusive references, lifetimes and object initialization: these need a semantics of statements, not just
    of types.
13. ~~Concrete instances of the headline theorems~~ (done, 2026-10-31: `Examples.v` instantiates `transitivity`,
    `substitution_lemma`, `member_read_sound`, `member_write_sound`, `invocation_sound`, `override_parameter`,
    `member_call_in_generic_code_sound` and `generic_member_call_with_bounded_variables_instantiated` on one program,
    `intersect` and `closestCommonSupertypeWith` given as a coarse meet and join, so that their premises are shown jointly
    satisfiable, not vacuous; the last two take `unify_terminates_on` of that program, which is open. Found: the
    termination conjecture was false, step 11)
14. ~~The conjectures over a wider grid~~ (done, 2026-10-31: `TypeGrid` grown from 75 to 277 types and from 5 to 11
    instantiations, with subtypes through several supertypes and parameterized ones, type parameters bounded by
    another and by an intersection, in-variant type arguments of unrelated types, intersections in type arguments
    and Nothing in variant positions. Found: `closest_common_supertype_of_classes` is false of the frontend (#17);
    `closest_common_supertype_keeps_bottom_only` is false of the frontend (#18); and `closest_common_supertype_is_above_both`
    failed for intersections of disjoint classes, which the join takes for `exclusive Nothing` (step 4) while unify
    didn't put them below it: `BoundIntersectionTypeReference.flippedUnify` now takes such an intersection below every
    type, as the bottom type is; the model's `intersection_flipped_unify` doesn't yet (open: it makes the lemmas that
    take a component of an accepted intersection, `Generics.flipped_some` and its kind, hold only of other
    intersections). Also found: the frontend crashes on `fn f<T : A & B, Q : A>(x: T & Q)`, roadmap 40. #17 and #18
    stay red in `CommonTypesTests` until the conjectures are reformulated)

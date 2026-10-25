# Proof coverage

What the proofs in [`theories/`](theories) cover of the type system, and what they don't. The premises
the proofs take are listed once, in the [readme](readme.md#what-the-proofs-assume); this file only
refers to them. Keep it up to date with every change to the proofs or to the type system.

✓ proven · ◐ proven in a weaker form, or under a conjecture · ✗ not covered

## Surprising blind spots

| # | what isn't covered | example | why |
|---|---|---|---|
| 3 | A type parameter made nullable inside a bound, in generic code where its bound isn't nullable; or the bounded parameter itself, made nullable, of a mutability given to it or narrowed, inside its bound, in generic code | `fn f<A : Any, B : List<A?>>` and `T : Ord<in T?>` called from generic code | The bounds of the theorems of generic code have type variables made nullable in type arguments only narrowed, as for parameters (#12), and the bounded variable itself only plainly (`bplain`: `args_narrowed`, `args_avoid`): with a candidate c in its place, `Ord<in c?>` or `Box<mut c>` isn't shown to be a mixed type (`mfrag`); outside of generic code, `B : List<A?>` is covered (`ifrag`, `nfrag`), and as the whole bound, `T : U?`, outside of generic code where the final values are class types (#10) |
| 4 | A bound mentioning another variable, with no argument giving that variable a lower bound | `fn f<A, B : List<A>>(a: A) -> B` | FBounded assumes such variables get a lower bound. Kotlin only reports an error when the variable is F-bounded; here it silently uses upper bound ∩ instantiated bound |
| 5 | Explicit type arguments for a function whose bounds mention type variables | `make::<Num>()` with `T : Ord<in T>` | FBounded only covers inference from arguments |
| 6 | Bounds containing `m T` or `T!` as a component of an intersection, other than narrowed | `T : A & mut U` | Of the components of intersections, the inference proofs admit `compfrag`: `ifrag`, and `U!`, as ofComponents narrows a component whose bound is nullable. In type arguments, `B : List<mut A>` and `B : List<A!>` are covered, outside of generic code where the final values are class types (#10), and in generic code but for the variable itself (#3); as the whole bound, `T : U!`, `T : m U`, `T : m U?` are covered (`pfrag`) |
| 9 | Receivers of a class whose type parameters' bounds aren't class types | `node.m()` with `class Node<T : Ord<in T>>`, `class Wrap<A, B : Holder<A>>` | The member-call theorems take class-type bounds for the type parameters of the class |
| 10 | Bounds that are neither class types nor types of the parameters, or with type variables in type arguments of a mutability given to them or narrowed, and parameter types with such type arguments, where the final values aren't class types, outside of generic code (◐‡) | `T : A & B` or `T : A & Ord<in T>` inferred to an intersection, `T : U?` or `T : U!` to a type parameter, `B : List<mut A>` or `x: Box<A!>` with `A` inferred to an intersection, in non-generic code | Premise of FBounded (of type arguments, where they aren't plain, `args_plain`): with it, every reference to a type parameter, of any mutability and `!`, is within its bound as those of a caller are (`WithinBounds.param_refs`), and an intersection of class types is below the instance of its components (`below_intersection_instance`), which take class-type bindings; non-generic code is covered only as generic code without type parameters of the caller, under its conjectures |
| 11 | Member reads and writes in generic code, or of non-plain member types | `box.value` with `box: Box<T>`; members typed `mut T`, `T!`, `A & T` | MemberAccess only covers class-type type arguments, and members typed `T`, `T?` or class types of those |
| 12 | Intersections as parameter types; in generic code, a type variable of a non-null bound made nullable in type arguments | `x: T & A`; `Box<T?>` with `T : Any`, called from generic code; the same for the type parameters of the class in member functions | The parameter types of all call theorems are `pfrag`: those of `ifrag`, nullable only class types (`no_generics`), with type variables in type arguments of a mutability given to them, narrowed, or made nullable (`nfrag`: `Box<mut T>`, `Box<T!>`, `Box<T?>`), and a type variable as the whole type, of a mutability given to it, narrowed, or made nullable (`m T`, `T!`, `T?`, `m T?`). In generic code, a type variable made nullable in type arguments is narrowed (`args_narrowed`), as the compiler builds `T?` of a nullable bound: of a non-null bound, its instance may be a nullable type parameter of the caller, which `gfrag` doesn't have in type arguments. A type of generic code given a mutability, the meet with its own, as instantiating `m T` gives it, is one (`GenericCode.caller_ref_apply`, through `wtfrag_given`), and its instance at run time is the instance given the mutability (`GenericReceivers.instance_ref_apply`). Outside of generic code, type arguments `m T` and `T!` take the final values to be class types (#10) |
| 13 | `Nothing` of any mutability but `exclusive`, in parameter types, bounds and the types of arguments, also in type arguments | `read Nothing`, `List<read Nothing>`, `mut A & read Nothing` | The fragments admit Nothing only as `exclusive Nothing`, as `read Nothing` isn't below every type in the frontend (`wf_nothing_is_not_const`); roadmap 35 would make every `m Nothing` behave like `exclusive Nothing` |

## Subtyping (unify)

| area | status | where |
|---|---|---|
| Class types (variance, ownership, nullability): transitivity, reflexivity | ✓ | `Transitivity.v` |
| Mutability promises are conflict-free; assignability respects mutability | ✓ | `Ops.v` |
| Const classes (fit every mutability) | ✓ | `Subtyping.v`, `Ops.v` |
| Type parameters, `m T`, `T!`, `T?`, intersections: transitivity | ◐ proven only to never reject; accepting rests on `unify_terminates` | `Generics.v`, `Conjectures.v` |
| Reflexivity on type parameters and intersections | ◐ same | `FinalValues.v` |
| Erroneous types | ✗ modelled in unify, no theorem | — |
| Ownership (`owned`/`ref`) | ✓ but not implemented in Kotlin | `Ownership.v` |

## Substitution (instantiating type parameters)

| area | status | where |
|---|---|---|
| Class types, `T`, `m T`, `T!`, `T?`, bounds mentioning other parameters, F-bounds | ✓ | `Substitution.v` |
| Intersections at the top level and as assignees | ◐ assumes `unify_terminates` | `SubstitutionTerminating.v` |
| Intersections inside type arguments (`Box<A & T>`) | ◐ assumes `unify_terminates` | `SubstitutionWide.v` |
| Explicit type arguments within declared bounds, including F-bounds | ✓ | `WithinBounds.v` |

## Member access

| area | status |
|---|---|
| Read and write through variant type arguments; members typed `T`, `T?`, class types of those; explicit ownership | ✓ `MemberAccess.v` |
| Member types `m T`, `T!`, intersections; type arguments of the object that aren't class types; generic code | ✗ (#12) |

## Calls and inference, by the callee's bound shape

Columns:

- **free fn**: a function without a receiver, called with class-type arguments.
- **member fn**: called on a receiver of class type, including subclasses, with class-type arguments; the type
  parameters of the class bounded by class types (#9).
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
| mentions another parameter made nullable in type arguments (`B : List<A?>`) | ✓* | ✓* | ◐*‡§ | ◐*‡§ | ◐*‡§ |
| mentions another parameter narrowed in type arguments (`B : List<A!>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter of a given mutability in type arguments (`B : List<mut A>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| F-bound (`T : Ord<in T>`, `T : Ord<in T>?`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| intersection with variables (`T : A & Ord<in T>`, `T : A & U` with `U : Any?`, a component `U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| nullable intersection with variables (`T : A? & Ord<in T>?`, `T : A? & U?`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter, narrowed (`T : U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter of a given mutability (`T : mut U`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| intersection with a component `m U` (`T : A & mut U`) | ✗ | ✗ | ✗ | ✗ | ✗ |

\* only when every such variable gets a lower bound from the arguments, and only for inference (no explicit
type arguments).
† only when the final values are class types.
§ only where the bound of the variable made nullable is nullable, as the compiler then narrows it (#3, #12).
◐ assumes the conjectures about `intersect` and `closestCommonSupertypeWith`, and `unify_terminates`; in generic code
also that the types of the arguments mention Nothing only as `exclusive Nothing`, and none of the callee's type
parameters as an ownership. Of an intersection bound, the final value is shown within each component (`bound_components`).

Of parameter types, type variables in type arguments are covered in the cells above: made nullable (`Box<T?>`)
in every column, in generic code only where the bound of the variable is nullable (#12); of a given mutability
or narrowed (`Box<mut T>`, `Box<T!>`) with † for free and member functions, and in generic code.

Within the covered cells, these are proven: explicit type arguments and receiver capture (`Inference.v`),
lower and upper bounds and the final values chosen (`Constraints.v`), receivers of subclasses with exact
supertype arguments (`MemberCalls.v`), final values that are type parameters or intersections
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
| Parameter and return types beyond class types and plain references to the class's type parameters (`m T`, `T!`, intersections) | ✗ | — |
| Functions with type parameters of their own | — Kotlin can't override them (roadmap 34) | — |
| Every function a concrete class inherits is implemented, so dispatch finds one | assumed: the compiler reports `AbstractInheritedFunctionNotImplementedDiagnostic` otherwise (`PossiblyMixedInBoundMemberFunction`) | readme, assumptions |

## Outside the model entirely

| area |
|---|
| Overload resolution |
| Constructors and object initialization (`PartialObjectInitialization`), mixins |
| Lifetimes and exclusive-reference tracking (`VariableLifetime`); `Ops.v` covers the static promises of references only |
| Declaration-site variance, which emerge doesn't have |

## Order of work

Towards full coverage, in this order, each step unblocking the next or removing the most risk for its cost:

1. ~~Override dispatch~~ (done: `Overrides.v`)
2. ~~Generic code with bounds that mention type variables~~ (done: free and member functions called from generic
   code, their instances, and calls on receivers of generic code, intersection bounds among them;
   `instantiate_free`, `GenericArguments`: `mixed_arguments`, `gstatic_whole`, `gleaf_all`,
   `generic_invocation_with_bounded_variables_sound`, `generic_member_call_with_bounded_variables_sound`;
   `GenericCode.generic_member_call_with_bounded_variables_instantiated`; `GenericReceivers`: `runtime_mixed`,
   `rstatic_whole`, `rleaf_all`, `generic_receiver_with_bounded_variables_sound`. With them arguments that aren't
   class types, formerly #8, and calls on receivers of generic code, formerly #7. Intersections of the fragment are
   uniform, their components assigned as one mutability, as `ofComponents` builds them)
3. The remaining type shapes, in that setting: of bounds, #1 closed intersections (done, of the bounds of the
   inference interface, as FinalValues has them: `static_bound`, `bindings_within` through `inter_accepts`), #2 nullable intersections (done:
   `inter_of`, `static_components`, `gstatic_components`, `rstatic_components`; of type variables among the components,
   `components_of`, `rewrap_takes`), #3 `T : U?`, #6 `m T` / `T!` (narrowed type variables among the components of an
   intersection done, as `T : A & U` with `U : Any?` has them: `Inference.compfrag`, `static_component_cases`,
   `narrowed_component`, `narrowed_variable_not_nullable`, `free_variable_any`; as the whole bound done, `T : U?`, `T : U!`, `T : m U`, `T : m U?`, in every setting: `Constraints.reference_step`, `static_whole`; `FBounded.bindings_within` through
   `WithinBounds.param_refs`, `mentions_of_static`; `gstatic_whole` through `mixed_parameter`;
   `rstatic_whole` through `runtime_mparameter`); of parameter types, #12 (a type variable as the whole type of a parameter done,
   `T?`, `T!`, `m T`, `m T?`, in every setting: `pfrag`, `pgeneric`,
   `unify_variable_given`, `Generics.target_ordered`, `instance_never_fails`, `parameter_step`,
   `exact_parameter`, `generic_parameter`, `mixed_parameter`, `runtime_parameter`, `runtime_mparameter`; type
   variables in type arguments of parameter types done, `Box<T?>`, `Box<T!>`, `Box<m T>`, in every setting but
   `Box<T?>` of a non-null bound in generic code: `nfrag`,
   `Inference.reference_target`, `reference_assignee`, `Constraints.nested_target_step`, `nested_assignee_step`,
   `Generics.instance_within_never_fails`, `MemberCalls.refs_fuel`, `FBounded.args_plain_candidate`,
   `GenericArguments.gnested_target`, `mnested_target`, `GenericReceivers.rnested_target`, `rmnested_target`; with
   them, of bounds outside of generic code, `B : List<A?>`, `B : List<m A>`, `B : List<A!>`; in bounds in generic
   code done, but `B : List<A?>` of a non-null bound and the bounded variable itself: `GenericArguments.bplain`,
   `mfrag_candidate`, `FreeInstances.plain_variables`, `other_ref_bound`, `GenericReceivers.nib_candidate`; `m T`
   instantiated and on generic receivers done, as the whole type and in type arguments, of parameters and bounds:
   `GenericCode.tfrag_given`, `wtfrag_given`, `caller_ref_apply`; `GenericReceivers.ground_given_target`,
   `runtime_mutability`, `instance_given`, `instance_ref_apply`. Next: `T : A & m U`, intersections as parameter
   types)
4. Inference variants and receivers: #4 no lower bound, #5 explicit type arguments, #9 receivers of classes
   with such bounds
5. Member access in generic code and of other member types (#11)
6. `unify_terminates`, which turns every ◐ into ✓
7. Exclusive references, lifetimes and object initialization: these need a semantics of statements, not just
   of types

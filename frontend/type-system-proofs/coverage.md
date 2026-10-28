# Proof coverage

What the proofs in [`theories/`](theories) cover of the type system, and what they don't. The premises
the proofs take are listed once, in the [readme](readme.md#what-the-proofs-assume); this file only
refers to them. Keep it up to date with every change to the proofs or to the type system.

✓ proven · ◐ proven in a weaker form, or under a conjecture · ✗ not covered

## Surprising blind spots

| # | what isn't covered | example | why |
|---|---|---|---|
| 3 | The bounded parameter itself, made nullable, of a mutability given to it or narrowed, inside its bound, in generic code | `T : Ord<in T?>` called from generic code | The bounds of the theorems of generic code have the bounded variable itself in type arguments only plainly (`bplain`: `args_avoid`): with a candidate c in its place, `Ord<in c?>` or `Box<mut c>` isn't shown to be a mixed type (`mfrag`). The other type variables made nullable in type arguments of bounds are covered, also of non-null bounds (`B : List<A?>` with `A : Any`): their values aren't nullable, as those of the lower bounds checked against non-null bounds aren't (`GenericArguments.gstatic_checked`) |
| 4 | A bound mentioning another variable, with no argument giving that variable a lower bound | `fn f<A, B : List<A>>(a: A) -> B` | FBounded assumes such variables get a lower bound. Kotlin only reports an error when the variable is F-bounded; here it silently uses upper bound ∩ instantiated bound |
| 5 | Explicit type arguments for a function whose bounds mention type variables | `make::<Num>()` with `T : Ord<in T>` | FBounded only covers inference from arguments |
| 9 | Receivers of a class whose type parameters' bounds aren't class types | `node.m()` with `class Node<T : Ord<in T>>`, `class Wrap<A, B : Holder<A>>` | The member-call theorems take class-type bounds for the type parameters of the class |
| 10 | Bounds that are neither class types nor types of the parameters, or with type variables in type arguments of a mutability given to them or narrowed, and parameter types with such type arguments or that are intersections, where the final values aren't class types, outside of generic code (◐‡) | `T : A & B` or `T : A & Ord<in T>` inferred to an intersection, `T : U?` or `T : U!` to a type parameter, `B : List<mut A>`, `x: Box<A!>` or `x: A & B` with `A` inferred to an intersection, in non-generic code | Premise of FBounded and MemberCalls (of type arguments, where they aren't plain, `args_plain`; of intersections as parameter types, `inter_of`): with it, every reference to a type parameter, of any mutability and `!`, is within its bound as those of a caller are (`WithinBounds.param_refs`), and an intersection of class types is below the instance of its components (`below_intersection_instance`), which take class-type bindings; non-generic code is covered only as generic code without type parameters of the caller, under its conjectures |
| 11 | Member reads and writes in generic code, or of non-plain member types | `box.value` with `box: Box<T>`; members typed `mut T`, `T!`, `A & T` | MemberAccess only covers class-type type arguments, and members typed `T`, `T?` or class types of those |
| 13 | `Nothing` of any mutability but `exclusive`, in parameter types, bounds and the types of arguments, also in type arguments | `read Nothing`, `List<read Nothing>`, `mut A & read Nothing` | The fragments admit Nothing only as `exclusive Nothing`, as `read Nothing` isn't below every type in the frontend (`wf_nothing_is_not_const`); roadmap 35 would make every `m Nothing` behave like `exclusive Nothing` |
| 15 | Intersections whose components keep their nullability, where one may be null only as its instance may: `A? & P`, `P & R` with `P, R : Any?` | `x: A? & U` with `U : Any?`; an upper bound `A?` and one `P` of the same variable | ofComponents makes `(A & B)?` only where every component is `X?`, non-null components where one isn't nullable, and otherwise keeps the components as they are, so that null is a value exactly where it is one of each component. The fragments (`gfrag`) have only the first two shapes, so the theorems don't cover these types, and `intersect_stays_in_fragment` doesn't hold of such operands. As instances of the components of parameter types, the argument is shown below them (`GenericArguments.below_of_components`), but not that they are of the fragment |

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
| Member types `m T`, `T!`, intersections; type arguments of the object that aren't class types; generic code | ✗ (#11) |

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
| mentions another parameter made nullable in type arguments (`B : List<A?>`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter narrowed in type arguments (`B : List<A!>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| mentions another parameter of a given mutability in type arguments (`B : List<mut A>`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| F-bound (`T : Ord<in T>`, `T : Ord<in T>?`) | ✓* | ✓* | ◐*‡ | ◐*‡ | ◐*‡ |
| intersection with variables (`T : A & Ord<in T>`, `T : A & U`, a component `m U` or `U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| nullable intersection with variables (`T : A? & Ord<in T>?`, `T : A? & U?`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter, narrowed (`T : U!`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |
| another parameter of a given mutability (`T : mut U`) | ✓*† | ✓*† | ◐*‡ | ◐*‡ | ◐*‡ |

\* only when every such variable gets a lower bound from the arguments, and only for inference (no explicit
type arguments).
† only when the final values are class types.
◐ assumes the conjectures about `intersect` and `closestCommonSupertypeWith`, and `unify_terminates`; in generic code
also that the types of the arguments mention Nothing only as `exclusive Nothing`, and none of the callee's type
parameters as an ownership. Of an intersection bound, the final value is shown within each component (`bound_components`).

Of parameter types, type variables in type arguments are covered in the cells above: made nullable (`Box<T?>`)
in every column, of non-null bounds too; of a given mutability or narrowed (`Box<mut T>`, `Box<T!>`) with † for
free and member functions, and in generic code. So are intersections, nullable or not (`x: T & A`, `x: T? & A?`),
with † for free and member functions, and in generic code: the argument is below the instance of the whole
intersection, as ofComponents makes it.

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
| Casts and instance-of checks (`as`, `is`): out of scope until there is runtime reflection on type arguments (roadmap 13); their type arguments go unchecked until then, by design |
| Constructors and object initialization (`PartialObjectInitialization`), mixins |
| Lifetimes and exclusive-reference tracking (`VariableLifetime`); `Ops.v` covers the static promises of references only |
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
3. ~~The remaining type shapes, in that setting~~, all but #3 and #15 (steps 9 and 8 below): of bounds, #1 closed intersections (done, of the bounds of the
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
   code done, but the bounded variable itself (#3): `GenericArguments.bplain`,
   `mfrag_candidate`, `FreeInstances.plain_variables`, `other_ref_bound`, `GenericReceivers.nib_candidate`; `m T`
   instantiated and on generic receivers done, as the whole type and in type arguments, of parameters and bounds:
   `GenericCode.tfrag_given`, `wtfrag_given`, `caller_ref_apply`; `GenericReceivers.ground_given_target`,
   `runtime_mutability`, `instance_given`, `instance_ref_apply`; intersections as parameter types done: `Inference.qfrag`, `below_intersection_instance`, `Constraints.param_components`, `parameter_step`,
   `MemberCalls.pbound_in_from_refs`, `FBounded.bindings_within`,
   `GenericArguments.below_of_components`, `gparam_components`, `generic_qparameter`, `mparam_components`,
   `mqparameter`, `GenericCode.caller_of_components`, `qinst_caller`, `qfree_caller`,
   `GenericReceivers.rparam_components`, `runtime_qparameter`. The model follows ofComponents in keeping the nullability of components that may be null only as their instance may (#15), with instantiated generic code taking the values of type parameters of non-null bounds to be non-null, as they are within their declared bounds: `GenericCode.values_not_nullable`, from the bounds of the type parameters of the callee being the declared ones and, in `generic_member_call_with_bounded_variables_instantiated`, the type arguments of the object within them, as `member_call_in_generic_code_instantiated` already took them. With explicit type arguments, intersections as parameter types done: `Inference.exact_components`, `exact_qparameter`, as `member_call_sound` has them. Whatever the final values, intersections as parameter types done: `GenericArguments.member_call_with_any_final_values_and_intersections_sound`; on generic receivers where the function's bounds mention type variables done: `GenericReceivers.rmparam_components`, `runtime_mqparameter`, and at run time, below the instance of each component, below that of the intersection ofComponents makes of them (`runtime_of_components`). `T?` of a non-null bound in type arguments there and in bounds done: a lower bound checked against a non-null static upper bound isn't nullable, as unify took it (`GenericArguments.gstatic_checked`, `gstatic_whole`, `variable_takes_not_nullable`), so neither are the final values of non-null bounds (`gfinal_not_nullable`), and the checks hold for bindings of such values (`nonnull_values`); on generic receivers, with the type arguments of the object within the bounds of the class)
Tests, of the Kotlin code:

4. The conjectures over more types (`CommonTypesTests`). Every ◐ rests on them.
   - Add to the grid the shapes the proofs now cover: intersections with type-variable components of a given
     mutability or narrowed (`A & read U`, `A & U!`), three components, `Box<T?>`, F-bounded parameters.
     Add #15's `A? & P` too.
   - Check the conjectures that aren't tested yet:
     - that the results stay of the fragment (`intersect_stays_in_fragment`,
       `closest_common_supertype_stays_in_fragment`, and the same in generic code);
     - `closest_common_supertype_keeps_bottom_only`;
     - `closest_common_supertype_of_classes`.
5. Kotlin's unify, for what the proofs show of the model's. Over the same grid, test:
   - transitivity and reflexivity;
   - that bindings within the bounds keep assignability when instantiated (`Substitution.v`);
   - that unify finishes, under a step or stack limit (`unify_terminates`). Use class tables with F-bounds and
     deep nesting that `ExpansiveInheritance.kt` lets through.

   A violation is a divergence between Kotlin and the model, or a counterexample to a conjecture.
6. End-to-end probes of the blind spots and of what is outside the model, likeliest first. Each probe tries to
   put a value where its type says it can't be: null into a non-null type, a `read` reference into `mut`, an `A`
   into a `B`.
   - #15 `A? & P`: the third case of `ofComponents` is new code, and `intersect_stays_in_fragment` doesn't
     hold of it.
   - #11 member reads and writes through variant type arguments in generic code, and members typed `mut T`,
     `T!`, `A & T`.
   - Exclusive references and lifetimes (outside the model): roadmap 20 is a known hole.
   - Overrides whose parameter or return types are `m T`, `T!` or intersections.
   - Partial object initialization and mixins (outside the model).
   - #9 receivers of classes with variable bounds, #4 variables without a lower bound, #5 explicit type
     arguments.
   - #3 `T : Ord<in T?>`: its bound narrows T while it is resolved (`isResolvingBound`).
   - #13 `read Nothing`.

   A hole found by any of steps 4 to 6 is fixed and proven next, before the steps below. Whatever a probe finds
   outside the model also goes into the roadmap.

Proofs:

7. #11 member access in generic code and of other member types; overrides beyond class types.
8. #15 intersections whose components keep their nullability: gfrag widened to them, and
   `intersect_stays_in_fragment` with it.
9. Inference variants and receivers, then the bounded variable itself: #9 receivers of classes with such
   bounds, #4 no lower bound, #5 explicit type arguments, #3.
10. #13, together with roadmap 35 (`Nothing` declared const), which changes what there is to prove.
11. `unify_terminates`, which turns every ◐ into ✓. It is last of the type system, as it isn't a soundness
    problem: if unify doesn't finish, the compiler rejects the program. Step 5 tests it meanwhile.
12. Exclusive references, lifetimes and object initialization: these need a semantics of statements, not just
    of types.

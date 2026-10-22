# Proof coverage

What the proofs in [`theories/`](theories) cover of the type system, and what they don't. The premises
the proofs take are listed once, in the [readme](readme.md#what-the-proofs-assume); this file only
refers to them. Keep it up to date with every change to the proofs or to the type system.

✓ proven · ◐ proven in a weaker form, or under a conjecture · ✗ not covered

## Surprising blind spots

| # | what isn't covered | example | why |
|---|---|---|---|
| 1 | Bounds that are intersections without type variables, anywhere | `fn f<T : A & B>(t: T)` | FBounded requires a closed bound to be a class type; the other theorems require class-type bounds |
| 2 | Nullable intersection bounds | `T : (A & Ord<in T>)?`, `T : (A & B)?` | Excluded by `static_bound` and by the class-type bounds elsewhere |
| 3 | A bound that is another type parameter, made nullable | `fn f<U, T : U?>` | A nullable type variable isn't a parameter type the inference proofs admit (`no_generics`) |
| 4 | A bound mentioning another variable, with no argument giving that variable a lower bound | `fn f<A, B : List<A>>(a: A) -> B` | FBounded assumes such variables get a lower bound. Kotlin only reports an error when the variable is F-bounded; here it silently uses upper bound ∩ instantiated bound |
| 5 | Explicit type arguments for a function whose bounds mention type variables | `make::<Num>()` with `T : Ord<in T>` | FBounded only covers inference from arguments |
| 6 | Bounds containing `m T` or `T!` | `B : List<mut A>`, `B : A!` | Not in the fragment FBounded admits |
| 7 | Calling a function with variable-mentioning bounds from generic code | `fn g<X : Ord<in X>>(x: X) = max(x, x)` | Generic-code theorems take bounds without type variables, and FBounded takes class-type arguments only |
| 8 | Arguments that aren't class types, for a function with variable-mentioning bounds | `max(ab, ab)` with `ab: A & B` | FBounded arguments must be class types (`afrag`) |
| 9 | Receivers of a class whose type parameters' bounds aren't class types | `node.m()` with `class Node<T : Ord<in T>>`, `class Wrap<A, B : Holder<A>>` | The member-call theorems take class-type bounds for the type parameters of the class |
| 10 | Intersection bounds with variables, where the final values aren't class types | `T : A & Ord<in T>` inferred to an intersection | Premise of FBounded |
| 11 | Member reads and writes in generic code, or of non-plain member types | `box.value` with `box: Box<T>`; members typed `mut T`, `T!`, `A & T` | MemberAccess only covers class-type type arguments, and members typed `T`, `T?` or class types of those |

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
- **from generic code**: arguments mention the caller's type parameters.
- **instantiated**: generic code with its type parameters bound at run time.
- **generic receiver**: `list.add(x)` with `list: List<T>`.

| callee's type-parameter bound | free fn | member fn | from generic code | instantiated | generic receiver |
|---|---|---|---|---|---|
| class type (`Foo`, `Any?`, `Box<X>`) | ✓ | ✓ | ◐ | ◐ | ◐ |
| closed intersection (`A & B`) | ✗ | ✗ | ✗ | ✗ | ✗ |
| another parameter (`T : U`) | ✓* | ✓* | ✗ | ✗ | ✗ |
| a type parameter of the class (`T : E`, `T : Ord<in E>`) | — | ✓* | ✗ | ✗ | ✗ |
| another parameter, nullable (`T : U?`) | ✗ | ✗ | ✗ | ✗ | ✗ |
| mentions another parameter (`B : List<A>`) | ✓* | ✓* | ✗ | ✗ | ✗ |
| F-bound (`T : Ord<in T>`, `T : Ord<in T>?`) | ✓* | ✓* | ✗ | ✗ | ✗ |
| intersection with variables (`T : A & Ord<in T>`) | ✓*† | ✓*† | ✗ | ✗ | ✗ |
| nullable intersection with variables | ✗ | ✗ | ✗ | ✗ | ✗ |
| contains `m T` / `T!` | ✗ | ✗ | ✗ | ✗ | ✗ |

\* only when every such variable gets a lower bound from the arguments, and only for inference (no explicit
type arguments).
† only when the final values are class types.
◐ assumes the conjectures about `intersect` and `closestCommonSupertypeWith`, and `unify_terminates`.

Within the covered cells, these are proven: explicit type arguments and receiver capture (`Inference.v`),
lower and upper bounds and the final values chosen (`Constraints.v`), receivers of subclasses with exact
supertype arguments (`MemberCalls.v`), final values that are type parameters or intersections
(`FinalValues.v`), and bounds with type variables, for free and member functions (`FBounded.v`:
`invocation_with_bounded_variables_sound`, `member_call_with_bounded_variables_sound`).

## Outside the model entirely

| area |
|---|
| Override checks (signature compatibility) and dispatch to overrides |
| Overload resolution |
| Constructors and object initialization (`PartialObjectInitialization`), mixins |
| Lifetimes and exclusive-reference tracking (`VariableLifetime`); `Ops.v` covers the static promises of references only |
| Declaration-site variance, which emerge doesn't have |

## Largest lever

Closed intersection bounds (#1) are the last ✗ in the "free fn" and "member fn" columns that a common program
hits. After that, generic code (#7): carrying `FBounded.v` over to `GenericArguments.v` onwards would fill
the remaining columns.

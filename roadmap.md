This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

0. **bug:** `catch` does not catch an exception thrown by a function that the `try` block calls; the program
   panics with "unhandled exception". Reproduces on linux-x86_64 with
   ```
   class TestError : Error {
       constructor {
           mixin ThrowableTrait("thrown on purpose")
       }
   }
   fn fail() {
       throw TestError()
   }
   mut fn main() {
       try {
           fail()
       } catch e {
           println("caught")
       }
   }
   ```
   Not investigated yet. There is no test that runs a compiled program, so nothing noticed (see the item on
   integration tests).
1. ~~signed `<=` compiles to `<`: the LLVM backend lowers `IrNumericComparisonExpression.Predicate.LESS_THAN_OR_EQUAL`
   on signed types to `SIGNED_LESS_THAN` instead of `SIGNED_LESS_THAN_OR_EQUAL`~~
2. ~~global variables are initialized in declaration order within a source file, but not in dependency order across
   files: a global that reads a global of another file can see it uninitialized~~
3. ~~isolate thread-unsafe global state~~ done with tokens, see [tokens-plan.md](tokens-plan.md): there is no
   mutable global state left; standard IO is reached through the unique classes `StandardOut` and `StandardError`,
   which `main` obtains from the root token it is given.
4. additional language constructs
   1. switch/when statement
   2. union types: `TypeA | TypeB | TypeC`
      * support exhaustiveness check on switch/when statements
   3. inferable types? Be able to mention `_` anywhere where inference is supported and have that part of the
      type be filled in by the compiler. Useful for the foreach syntax sugar: range: mut InputRange<_> = iterable.asRange()
5. Stdlib basics
6. Stdlib basics
    * some good standard collections
    * ArrayList, LinkedList, (De)Queue, Stack, ...
      * hashCodes: Java-style is overkill, have an explicit Hashable interface
    * Map
    * string templates
      * interpolation like in Kotlin instead of concatenation like in Java or D
      * make that work with the Printable interface. So e.g. a template "a ${x} b ${y} c" desugars to an
        memory-buffered printstream, with calls to put of "a ", x.printTo(...), " b ", y.printTo(...), " c"
    * I/O facilities. These should be blocking-style for now. It's the simplest to implement. Plus: if emerge ever
      adds async task orchestration, it will be either full-blown coroutines (all code is a coroutine, like in go)
      or futures. Futures is a major rewrite of emerge code anyhow, but changing blocking IO to coroutine IO is transparent
      to the emerge code.
6a. internal mutability: state that can change through a `read` reference to the object holding it. Needed for
    lazy initialization, and for classes that offer reading through something they have to mutate to do so (a
    `read S3Bucket` sends its queries through a socket stream)
    * `Cell<T>`, a class in `emerge.core` whose operations are intrinsics and take `self` as `read`:
      `fn get(self: read _) -> T`, `fn set(self: read _, value: T)`. What a cell holds is not part of the state of
      the object holding the cell
      * with function purity, `get` is a `read fn` and `set` a `mut fn`: the purity checks reason from mutability
        (a global of a `const` type is a compile-time constant, a write is a use as `mut`), and a cell reachable from
        a `const` global would be global state they don't see. So cells can't be used in `pure` functions
      * with tokens (`tokens-plan.md` on the branch `token-protected-global-state`), `token class Cell<token T>`
        instead: never `const`, every class holding one is a token class, none is reachable from a global or from
        another thread. The price, accepted: for a token class with a cell, that a `read` reference only observes
        is a promise of its author, not something the compiler checks. That code without a token cannot touch
        external state stays checked
      * type arguments cannot be `own` (item 19), so a cell hands out references of the mutability of `T`
    * `Lazy<T : const Any?>`, an intrinsic of its own, not built on `Cell`: a class with a lazy member must stay
      freezable and must not become a token class. `fn get(self: read _) -> T` runs the initializer on the first
      call. The time of that call must not show in the value, so the value is `const`, and the initializer
      captures only `const` data and no token; being `pure` is not enough, a pure function can read mutable data it
      captured. Needs function types (item 13) that can say so
7. ALPHA TESTABLE MILESTONE; At this point, the language should be powerful enough to tackle advent of code challenges.
    Todo: actually try and solve some!
8. integration tests!! Include emerge source code in this repository that tests the runtime and correct compilation.
    The unit tests in the frontend test the negative cases; these should test the positive ones. E.g. that 2+3=5,
    refcounting, control flow + exceptions, ...
9. integrate valgrind into the integration tests and check every test case. Fix the memory leaks that are discovered;
   already known:
   1. call arguments that are neither anchored nor reference-counted leak, e.g. `sumS32(holder.data!!)`:
      `BoundInvocationExpression` increments their reference count before the call, but after the call only drops
      the arguments that were reference-counted to begin with. A `capture` parameter passed on is such an argument:
      `fn f(capture a: read Array<S32>) = a.slice(1, 2)` leaks a reference to the array, and so does `arr[r]` with a
      range value `r`, because `Array.getAtIndex(UWordRange)` is such a function
   2. `f()!!.member` leaks the result of `f()`: the temporary from the invocation is never dropped when the
      not-null assertion and member access are chained onto it. Assigning it to a variable first doesn't leak
   3. autoboxes leak at conversion sites that have no owner: a box (`S32Box`, `ArrayBox`, ...) created for the result
      of an `if`/`try` branch or a `?:`, or for a temporary whose declared type differs from the value's, is never
      dropped. An `ArrayBox` keeps its array object alive with it, but never dangles. Call arguments, assignments,
      returns and invocation results move or drop their boxes correctly
10. documentation and presentation
    * from a user perspective. Github pages?
      * language syntax and semantics, maybe a good tutorial
      * design decisions, philosophy and reasoning
    * from a maintainer perspective
      * compiler architecture
      * llvm patterns
      * debugging techniques
    * add fix suggestions to diagnostics; this should also make them much more comprehensible
11. user tooling
    * language server and VSCode plugin
    * think about an assistant, e.g. taking care of these tasks
      * manage installed toolchain versions, at least on linux
      * automate grunt work like
        * setting up a new project including bazel build
        * adding modules or dependencies to existing projects
        * if emerge ecosystem/libraries are already a thing: manage dependencies
12. checked casts with type arguments. Type parameters are reified: every generic function receives the runtime
    type of each of its type parameters as a hidden argument, every generic class stores them in hidden fields, and
    every array object knows its element type (`emerge.core.reflection.Type`, `NamedType`, `IntersectionType`,
    `TypeArgument`; `typeOf::<T>()` yields it). `is` and `as` still only check the base type
    (`BoundInstanceOfExpression.validateTypeCheck` drops the type arguments). Remaining work:
    1. implement `isSubtypeOf` on `Type`, like the compiler does for `BoundTypeReference`
       * how to keep these in sync?? Tests, tests, tests!
    2. implement wildcard generic parameters to address unchecked generics, where the wildcard is always
       treated as if it was the bound of the parameter. E.g. given `class Pair<out A, out B>`,
       `x as Pair<String, *>` is treated like `Pair<String, Any?>`
    3. use that check in `is` and `as`. Afterwards, an `Array<String>` must not possibly be referenced as an
       `Array<S8>`
    4. mutability is not part of the runtime type information, so a cast may only keep or weaken the mutability
       (`x: read Any; x as read Foo` is fine, `x as mut Foo` is a compile-time error). In argument positions the
       source type says nothing about (`x: read Any; x as Array<mut Foo>`), only `read` is allowed; `own` is
       never a cast target. Today `BoundCastExpression` takes the mutability as written, which is a soundness hole
       independent of type arguments
13. Function types
    1. add function types to the grammar and type system.
       * do it like Kotlin where function types are syntax sugar for `FunctionN<...>`?
         (`(A, B) -> C = emerge.core.Function2<A, B, C>`)
    2. ~~deal with the higher-order function purity problem~~ there is no function purity any more. What is
       left of the problem is a rule for closures: a closure that captures a token is a token
       (rule 6 in [tokens-plan.md](tokens-plan.md)).
    3. implement references to top-level functions
    4. implement `foo()` where `foo` is an expression of a function type
       * !! edge case: `objectRef.foo()` where `foo` is a property of a function type
    5. implement lambda functions
       * syntax idea
         * single expression lambda: `fn (a, b) -> a + b`
         * code-chunk lambda: `fn (a, b) -> { ... ; ... ; return x }`
         * what about implicit `it` for single-parameter function types? `fn -> it.foo` and `fn { it.foo }`?
    6. implement last-argument lambdas like in Kotlin?
       * `fn a(p1: S32, p2: () -> Unit)` and invoke like `a(3) { /* lambda body */ }`
14. functional-style collection operations
    1. start simple with forEach
    2. go on with filter, map, fold, ...
    3. more tricky: make sure the code emitted by LLVM doesn't actually do all the allocation. A chain of maps and filters
       should be compiled down to a single loop.
15. import aliases: `import emerge.platform.print as platformPrint`, `import emerge.std.HashMap as DefaultMutableMap`
16. optimize reference counting; see [](refcounting optimizations.md)
    * for this, the logic to determine where reference counts are needed must move from the LLVM backend to
      the frontend; the frontend has the tools to deal with the complexity, the backend doesn't. Especially
      temporary values are BAD offenders
17. typealiases
18. smart casts
19. ~~fix loophole in the typesystem: a type parameter could be bound to an `own` type
    (`Array.new::<own Foo>(20, Foo())`, `Box<own Foo>`, `fn g<T>(x: T) -> T` called with an `own`
    value), though generic code makes any number of references to a value of type `T`~~
    Type parameters are never bound to an `own` type now: it is an error as a type argument or in the bound of
    a type parameter, and where inference only has `own` values for a type parameter it picks the mutability
    the bound or the expected type ask for, `mut` otherwise. `own T` on a parameter or return type is still
    an `own` reference to a value of the type argument.

    What remains: generic code can't hand an `own` value through and keep it `own`
    * `Array.slice`, `Array.sliceOrPanic` and `Array.getAtIndex` with a range are declared
      `fn slice<A : read Array<out Any?>>(capture self: A, ...) -> A`; the slice of an `own` array used to be
      `own` and is `mut` now, so it can't become a `const` array anymore. Same for every function of the shape
      `fn keep<A : read Foo>(capture self: A) -> A`.
      Possible fixes, undecided:
      * a second function with the mutability on the parameter and return type:
        `fn slice<A : ...>(capture self: own A, ...) -> own A`. Needs either another name, or overload
        resolution that prefers it for `own` arguments; and a second intrinsic in the backends
      * type parameters that opt in to being bound to `own` types, in whose scope a value of that type is
        treated like an `own` one: capturing it ends its lifetime (compare `~Copyable` in Swift)
      * make `own` a property of the variable/parameter/return value instead of the type, like `borrow`; then
        the question doesn't come up in the type system at all, but every expression has to carry it
    * a container that holds `own` values (`Channel<T>`, `Mutex<T>` with `fn take(self: mut _) -> own T`)
      can take them through a parameter typed `own T`, but can't be implemented in emerge: member variables
      can't be `own`, and a `T` read from one isn't. Needs `own` member variables with a take/swap
      operation, or intrinsics
    * a variable declared without a type and initialized from such a call is `read`, not `const` as it is for an
      `own` initializer: `y = g(Foo())` is a `mut Foo` joined with the `const` of the declaration. The expected
      type only takes part in inference when the variable has a declared type
20. optional parameters
    * parameter with default value is optional
    * affects overload validation and resolution
    * default value should be evaluated on the caller side because it allows to keep the
      ABI calling conventions
      * as a consequence, only the initial declaration of a function can declare default values,
        overrides cannot
21. Declaration-Site variance
    * support declaration-site variance: `class Pair<out A, out B> { ... }`. Anticipated problems:
      * assignment to member vars that have a generic type referencing an in/out type parameter can only
        be assigned on construction -> must not be "var"
      * the code generated in the constructor for the assignment won't validate, precisely because it's
        not generally valid to assign to an out-variant/in-variant member var -> needs an exception
      * it was partially supported before; some test-cases are already present but disabled
22. named arguments
    * allow to change the order of arguments? It's important to keep the evaluation order on the
      calling side to match the order of the arguments as passed, not as declared
23. threading
    A big point with the explicit-mutability types is to simplify multithreading (though, the other
    big benefit of them is the assemble-then-return-as-const pattern). Avoiding the complexity of 
    having a `shared` mutability like D allows to infer some properties necessary for multithreading:
    * mutable global state as in D: it is not shared across threads. Each thread has its own copy,
      starting a new thread re-initializes the mutable global state as defined in the source (as opposed
      to copying it from the parent thread).
      * maybe even ditch global state all together? Is that feasible / sensible?
    * "Dont communicate by sharing state, share state by communicating": there are no shared objects between
      threads. We'll have an actor model like Go or Erlang, where each thread as a (typed) inbox and receives
      messages from other threads on which it can act.
    * When sending a value to another thread, that thread gets a _deep copy_ of that value. This avoids having
      to do the runtime reference counting with atomics. It is only allowed to send `immutable` references
      to other threads. This has two crucial benefits:
      * it makes the necessary copy operation opaque / hide-able
      * it prevents the possibility of sending resource pointers (like file handles) to other threads (these
        are always mutable), avoiding the un-solvable problem of "how do i make a copy of a resource pointer?"
      * It can be optimized in the guts of the channel impl: if a value is to be sent to another thread
        and its reference count is `1`, then no copying is necessary.
    * there should be ready-made open-source Erlang-like channel implementations in C that the stdlib can
      use, making it feasible to implement
    * This complicates lambda literals that capture values by reference. Is it possible to copy these?
      Or should lambda literals that capture references have `read` mutability to prevent them from being
      sent across threads? This is important to get a decent WorkerThread/ForkJoinPool API.
    * On the matter of ForkJoin/WorkerThread: this would necessitate a Futures API:
      ```
      val futureVal: Future<S32> = forkJoinPool.submit({ doExpensiveComputation() })
      ```
      Which brings the important question to the table: Push-Based or Pull-Based futures?
    * the `take` function of a `unique class` has to be thread-safe: one instance per _process_, whichever thread
      asks first. Today the flag that knows whether the instance was handed out is a global variable like any
      other, which makes it thread-local (the LLVM backend emits globals as such), and `take` reads and sets it
      in separate steps. With threads the flag has to be one per process, and checking and setting it one atomic
      step; a constructor that throws has to release it again. See `UniqueClassCode` in the frontend.
24. review which other predefined classes should be declared `: const Any`: `String`, `ReflectionBaseType`,
    `StackTraceElement` and the boxes of the platform module (`S32Box`, ...) are never mutated after construction.
    Declaring them const changes what their fields read as and lets their values fit any mutability
25. ~~reconsider the name `exclusive`~~ it is `own` now: an `own` reference promises that no other reference can
    mutate the object or rely on it not changing, not that there are no other references (`read` aliases are
    allowed). The compiler still calls the `borrow`/`capture` axis "ownership" (`VariableOwnership`), which wants
    another name now
26. diagnostics about the static bound of a type variable show the other type variables in it, not their values:
    `b.ordered(Bad())` with `b: Box<Num>` and `fn ordered<T : Ord<in E>>` reports `Required: read Ord<in Var(E)>`
    instead of `read Ord<in Num>`
27. a member function with type parameters of its own can't be overridden: findOverriddenFunctions compares the
    parameter types by equality, and the type parameters of the override are never those of the overridden function
    ```
    interface Base {
        fn m<T>(self, t: T) -> T
    }
    class Sub : Base {
        override fn m<T>(self, t: T) -> T { return t } // Function m doesn't override anything
    }
    ```
    The type parameters would have to be matched up by position, their bounds compared, before comparing the
    parameter types. This is a usability problem, not a soundness one
28. parentheses in type notation, to group: `(A & B)?`. Today a nullable intersection can only be written with every
    component nullable, `A? & U?`, from which ofComponents builds `(A & U)?`; that spelling hides that the components
    get narrowed (`U?` with `U : Any?` becomes the component `U!`)
29. decorated member variables (`decorates value: T = init`) are rejected as not supported yet, as they weren't sound.
    The constructor ties the mutability of the object, `_M` in its return type `own W & _M`, to that of each
    decorated value through a parameter typed `X & _M`, and reading a decorated member gives it the mutability of the
    object. Three things broke that:
    * a member typed as a type parameter of the class got no such parameter (it's "already generic"), so
      `mut Holder<const X>` could be constructed from a `const X` and its member read as `mut X`. Tying it like the
      others, through a parameter typed `T & _M`, is rejected: assigning that parameter to the member typed `T`
      reports "cannot be proven to be a subtype of T". Not because of the common mutability of intersections (`read T`
      instantiates to the instance of `T` met with `read`, so it is `T` for a read bound); not looked into yet, but
      likely why the shortcut was added
    * a constructor call assigned to a `mut W` right away (`w: mut W = W(constX)`) is accepted, where the same
      signature as an intrinsic function (`fn ctor<_M, _V : X & _M>(v: _V) -> W & _M`) isn't; not looked into yet
    * writes to a decorated `var` member take the declared type, not the mutability of the object: a `read X` can
      be written into a `mut W` and read back as `mut X`

    `_M` likely wants to be a mutability-only parameter rather than an intersection component. The tests in
    `ClassErrors` ("decorated members") and `DecoratorMutabilityTests` describe the intended behaviour
30. `Array.trimmed` (and `String.trimmed` on top of it): copies a slice into a fresh array object of exactly the
    slice's size, so the rest of the base array can be freed. `U64.toString` returns a slice of its 21-byte buffer,
    keeping the entire buffer alive for as long as the string lives
31. various optimizations collected over time
    * static dispatch for mixed-in functions when the concrete type of the mixed-in object is known
      at compile time
32. model the frontend's rule that an intersection of disjoint classes (`N & M`, `N & Box<A>`) is below every type, as
    the bottom type it simplifies to (`BoundIntersectionTypeReference.flippedUnify`, coverage step 14): in the model,
    `Subtyping.intersection_flipped_unify` returning the carry where `is_effectively_bottom_type` holds of the
    components. It is the one entry of `OracleGrid.unify_excuses` (1049 pairs of `TypeGrid`) and the excuse of
    `closest_common_supertype_is_above_both`, and widening `GenericArguments.bottom_only` for #18 rests on it.
    Transitivity needs a lemma that what an effectively-bottom intersection accepts is below every type; the lemmas
    that take a component of an accepted intersection hold only of the other intersections then:
    `Generics.flipped_some`, `Ops.intersection_flipped_unify_found`, `Substitution.unify_into_components` and their
    ~50 call sites, and the mutability lemmas need side conditions or an `own` assignment mutability for such
    intersections. A sibling of item 39: both make the model's unify the frontend's where they differ today
33. runtime type information is allocated per call: a generic function calling another generic function with
    a type argument that mentions its own type parameters (`Array<T>`, `T?`) builds `NamedType`/`TypeArgument`
    objects on every call (`lowerReifiedType` in the LLVM backend). Cache them per call site, or intern
    structurally equal types
34. a virtual function overriding an interface function whose return type is a type parameter (`fn make(self) -> R`)
    with an array return type (`override fn make(self) -> Array<U>` for `Maker<Array<U>>`) crashes: the interface
    returns a boxed reference, the override returns an `arrayslice` struct, so the LLVM signatures differ and the
    override misreads its `self`. Needs a bridge like the ones `emerge.platform.ArrayBox` has, or the override has
    to use the representation of the overridden function
35. if interfaces ever get default method implementations, their type parameters need runtime type information
    too: a per-class vtable entry mapping the interface's type parameters to the class's hidden fields
36. the type system model picks other final values than the frontend where a type variable only has `own` values
    (item 19): `Constraints.final_value` is the lower bound, `TypeUnification.getFinalValueFor` gives it the
    mutability the upper bound asks for, `mut` otherwise (`VariableState.mutabilityForOwnValues`), and it is an
    error where the upper bound asks for `own` (`VariableState.needsOwnValue`). The theorems on calls are about
    the model's final values; nothing checks the difference, the oracle doesn't cover inference. To do:
    * `final_value` as the frontend has it, and "no variable needs an `own` value" as a premise of the theorems
      that take final values
    * a new obligation of `inference_types`: a bound that takes an `own` lower bound takes it with the mutability
      picked, too; shown for each instance (class types, generic code, generic receivers). `unify_root_mutability`,
      `frag_with_mutability` and `tfrag_given` are close to what it needs
    * the proofs that unfold `final_value` (it is used ~140 times in 9 files)
    * the type the call is expected to return, as one more constraint before the final values are picked
      (`TypeUnification.plusExpectedTypeForOwnValues`)
37. remove owned and ref slots from the type system model. They are specified and proven there, but not implemented
    and not going to be: each member variable or element of a generic data structure would either own its object,
    making it part of the holder (`lines: owned mut List<owned mut Line>`), or refer to it
    (`customer: ref const Customer`). Internal mutability is what was wanted of it, and `Cell` (item 6a) gives
    that for much less. The frontend is modelled as the types whose type arguments are all `ref`, or of the
    ownership of their type parameter, so nothing is wrong meanwhile; but every theorem speaks about an ownership
    the language doesn't have, and `owned` reads like the mutability `own`. To remove:
    * `Ownership.v`
    * `Model.Ownership` and the ownership of `Model.TypeArgument` (~750 uses of `TypeArgument` in 29 files),
      `parameter_ownership` and `any_ownership` (in up to 19 files)
    * `Subtyping.ownership_is_assignable_to` and its check in `unify_type_argument`
    * what part (a) of `Ops.v` says about owned parts: the `adopt` transition, and extracting a part
    * the ownership `RocqGridEncoder` writes for every type argument (`RocqOracleTests.kt`)
    * the mentions in `readme.md` and `coverage.md`

    Mostly deletion, but in nearly every file, and a full check of the model takes a while; do it apart from
    item 36, which changes the same files
-----
38. near future: reject identifiers that start with `__` in user code. The prefix is reserved for the identifiers
    the compiler generates (the flag of a `unique class`, the variables of a desugared `foreach`, type parameters
    of constructors, finalizers). As long as the check is missing, code in the same file as a `unique class` can
    assign the flag and obtain a second instance.

## Future features

### Refactoring bucketlist

* denote all identifiers quoted from input source that appear in diagnostics. Is already done
  sporadically -> do systematically
* give every diagnostic type a code (like typescript does)
* make CTContext.findInternalVariableName and .findInternalTypeName work before binding is complete
  If they are called before, they will settle imports. And some imports might decide they are erroneous
  because the symbol they import will only be bound later.

### Stateless Singletons

Emerge can't have Kotlins `object` singletons because that suggest a single identity per program execution,
but due to how all other state works, it would be an identity per thread. That complicates sending these
singletons across threads even more complicated. The possible solution: atoms. Like in functional and logic programming,
atoms are stateless identities. Because they're stateless they can retain their identity across all threads, just
like string literals/constants. They could even implement interfaces. Atoms can come in handy together
with algebraic data types to form Java-Like enums:

    atom A {}
    atom B {}
    atom C {}
    typealias Enum = A | B | C

State external to the program is not a case for atoms: it is modelled by tokens, and a resource there is one of
per process by a `unique class` (see [tokens-plan.md](tokens-plan.md)).

### Feed LLVM with all info available

Without targeting specific optimizations, it probably still helps performance to feed LLVM all information that is
available. These are possible (not exhaustive):

* `zeroext` / `signext` on numeric and boolean return values
* `dereferenceable(<n>)/dereferenceable_or_null(<n>)`
  * parameters
  * return values
  * stack read results
  * heap read results (object member access)
* `nofree` for borrowed parameters
* `noundef` - for everything??
* `readnone` - for unused parameters
* `readonly` - for readonly/constant parameters
* `nounwind` on functions, as exceptions use the regular return path in LLVM
* `inbounds` on most getelementptr instructions. the current DSL already goes.to great lengths to ensure that, so it's probably safe to assume the constraints for `inbounds` are never violated
* `nosync` on all/most emerge functions. the language is single threaded right now. once multi threading comes in the form of executors and channels, the channel API must somehow be made to not have the `nosync` attribute
* weights for branches
  * mark the exception path on function invocations as unlikely
  * mark the exception branch on fallible math as unlikely
  * loop header conditions should be heavily likely - after all, loops are supposed to be run often

### Forced Type Mutability

For some types, certain mutabilities don't make sense. E.g. a `const Weak` doesn't make any sense 
as the weak reference can turn `null` at any point.
For primitive number types (and for strings, too, probably), mutability doesn't make sense, so they
can always be `const`.

-> Allow the programmer to express this in the type definition

Could e.g. be

```
const class S8 { }

read class Weak<T> { }
```

For `Weak`, this is a bit tricky. `read` is the middle ground between `const` and `mut`, so declaring a
class as `read` doesn't say to which side it should gravitate. It might need to be `read|mut class Weak<T>`

### API comparison tool

A tool that can compare the source-code API of two modules. This can fulfill two use cases:

#### Help with library versioning

When releasing a new version of a library that is of the same major version as the previous release, automated tooling can
assist in assuring backwards compatibility by ensuring the new version doesn't break any source-level APIs. This could work
as a tool that can be given two versions of the same module and would output:

```
class ToolOutput {
  breakingChanges: List<ApiChange> = init
}

interface ApiChange {
	location: Span
	message: String
}
// and then e.g.
class TypeRemoved : ApiChange {
	name: CanonicalElementName
	override message = "Type ${name.simpleName} is no longer available."
}

// given
class Span {
	file: String = init
	fromLine: S32 = init
	fromColumn: S32 = init
	toLine: S32 = init
	toColumn: S32 = init
}
```

So, to the user, it could be shown like this:

```
[ERROR] Breaking change in minor version release: Type com.foo.bar.Frobnicator is no longer available.

in previous/src/Frobnicator.em:
   9 |
  10 | class Frobnicator {
     |       ^^^^^^^^^^^
  11 |
```

#### Assuring portability of emerge code

The `emerge.platform` module already has it's API defined in [backend-api](backend-api/src/main/emerge/noop-backend-platform).
To assure that code outside of `emerge.platform` remains portable, the build process of the compiler should assure
that all implementations of `emerge.platform` expose the **exact same** API as the abstract module. This makes sure that
all platforms implement the complete API, **plus** it makes it impossible for some emerge code to be tied to a specific
platform because the platform is not allowed to expose APIs exclusive to itself.

### Invariants

Steal from D

Classes and traits can define invariants. Those are checked
* after construction
* at the end of each method that can modify the receiver

```
class Foo {
    var x: S32 = init
    
    invariant {
        assert(x.rem(4) == 0)
    }
    
    fn addToX(self: mut _, valueToAdd: S32) {
        prevX = self.x
        set self.x = 3 // this does not trigger the invariant
        set self.x = prevX + valueToAdd
        // here, the invariant gets checked
    }
}

a = Foo(3) // panics due to the violated invariant
b = Foo(4) // okay
b.addToX(4) // this works; the temporary violation of the invariant is ignored
b.addToX(3) // this panics due to the violated invariant
```

#### Contract programming

Also steal from D?

### Emergent properties
Statements about the state of an object, e.g. isAbsolute on Path:
```
class Path {
    val segments: Array<String>
    property Absolute(self) = self.segments[0] != ""
}
```
It is derived from fields of an object. Because of mutable objects, it can only read fields that
are constant across the lifetime of the object. These could be marked with `final`, so e.g. interfaces
can declare properties, too, regardless of how the values are implemented. On all impls of final fields,
the compiler then has to verify that the field is not mutable, assigned at construction time or derived only
from other final fields.
Alternatively, the property could declare `immutable` on the `self` argument, making the property only available
on `immutable` references to that type, e.g.:

```
class List {
    property Empty(immutable self) = size == 0
}
```

You could then reference these properties in APIs, further strengthening the contract:
```
fun reduce(readonly self: List<out T> + !Empty, reductor: (T, T) -> T) -> T {
```

And callers would then first have to check for that property, smart-casts enabling sane UX:
```
val myList: List<S32>
val result: S32 = if (myList !is Empty) myList.reduce(S32::plus) else 0
```

Properties could also subtype each other, meaning that one property implies the other:
```
class List {
    property Empty(immutable self) = size == 0
    property Singleton(immutable self) : !Empty = size == 1
}
```

#### What's the purpose?
This could enable some level of dynamic typing: properties are simple types, and can be present
on a value based on its state, not based on the implementation. Simplifies inheriting multiple
interfaces in the presence of multiple implementations.

### CTFE

How complicated? Running stuff is probably easy, deducting *what* to run is probably hard.
Also, the CTFE needs a strict timeout (maybe user-configurable?) so when it runs an infinite loop,
it eventually continues.

[1]: https://openjdk.org/jeps/447

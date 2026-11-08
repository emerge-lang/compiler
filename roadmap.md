This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

1. explicitly importing a function from `emerge.std` makes invocations of it ambiguous: with
   `import emerge.std.println`, `println("x")` reports "Multiple overloads of println apply", listing one
   candidate
2. signed `<=` compiles to `<`: the LLVM backend lowers `IrNumericComparisonExpression.Predicate.LESS_THAN_OR_EQUAL`
   on signed types to `SIGNED_LESS_THAN` instead of `SIGNED_LESS_THAN_OR_EQUAL`
3. global variables are initialized in declaration order within a source file, but not in dependency order across
   files: a global that reads a global of another file can see it uninitialized
4. `EmergeLlvmContext.getArrayObjectType` chooses the array object type (and with it the raw element accessors) from
   the static bound of the element type: `Array<T>` with `T : Printable`, or `Array<out Printable>`, is accessed as
   an array of references. But an `Array<S32>` is a valid argument for both (`S32` is a `Printable`) and stores raw
   32-bit values, so the access reads/writes garbage. Only `Any` is handled correctly as a bound. Element bounds
   other than `Any` that have value-type subtypes need the virtual accessors (or the exact element type)
5. the compiler crashes (`InternalCompilerError`: `preprocessedInheritanceTree` accessed before semantic analysis
   phase 1 is complete) on an intersection of different base types in the type arguments of a supertype whose
   virtual functions are inherited:
   ```
   interface A {}
   interface B {}
   interface I<T> {
       fn put(self, x: T)
   }
   class C : I<A? & B?> {
       override fn put(self, x: A) {}
   }
   ```
   `InheritedBoundMemberFunction.semanticAnalysisPhase1` checks the receiver, and so unifies the type arguments,
   before the inheritance trees of `A` and `B` are built
6. the compiler crashes (`IllegalStateException`: this should have been prevented in ofComponents, from
   `BoundIntersectionTypeReference.validate` through `asRootResolved`) on an intersection of a type parameter bounded
   by an intersection with another type: `fn f<T : A & B, Q : A>(x: T & Q)`, `fn f<T : A & B>(x: T & C)`
7. isolate thread-unsafe global state
   * standard IO. E.g. the `main` function could receive an optional parameter that carries with it fields
     that hold stdin, stdout, stderr. At a later point, these can be sent to other workers/threads. That would
     require a builtin that asserts a certain stack-variable is exclusive, but that doesn't seem impossible to provide.
   * anything else to take care of?
8. additional language constructs
   1. switch/when statement
   2. union types: `TypeA | TypeB | TypeC`
      * support exhaustiveness check on switch/when statements
   3. inferable types? Be able to mention `_` anywhere where inference is supported and have that part of the
      type be filled in by the compiler. Useful for the foreach syntax sugar: range: mut InputRange<_> = iterable.asRange()
9. Stdlib basics
10. Static initialization order
    Currently, static initializers (e.g. top level variable initializer expressions) are executed in an
    undefined order. Circular dependencies within one file are prevented currently; across files is possible
    currently and that can lead to reading uninitialized memory. This either needs to be prevented.
11. Stdlib basics
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
12. ALPHA TESTABLE MILESTONE; At this point, the language should be powerful enough to tackle advent of code challenges.
    Todo: actually try and solve some!
13. integration tests!! Include emerge source code in this repository that tests the runtime and correct compilation.
    The unit tests in the frontend test the negative cases; these should test the positive ones. E.g. that 2+3=5,
    refcounting, control flow + exceptions, ...
14. integrate valgrind into the integration tests and check every test case. Fix the memory leaks that are discovered;
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
15. documentation and presentation
    * from a user perspective. Github pages?
      * language syntax and semantics, maybe a good tutorial
      * design decisions, philosophy and reasoning
    * from a maintainer perspective
      * compiler architecture
      * llvm patterns
      * debugging techniques
    * add fix suggestions to diagnostics; this should also make them much more comprehensible
16. user tooling
    * language server and VSCode plugin
    * think about an assistant, e.g. taking care of these tasks
      * manage installed toolchain versions, at least on linux
      * automate grunt work like
        * setting up a new project including bazel build
        * adding modules or dependencies to existing projects
        * if emerge ecosystem/libraries are already a thing: manage dependencies
17. runtime checks for generic parameters
    * does that need to be enabled by the programmer? Could be e.g. `class Array<reflect T>` if necessary
    * how to represent at runtime?
    * implement checked casts
      1. implement wildcard generic parameter to address unchecked generics, where the wildcard is always
         treated as if it was the bound of the parameter. E.g. given `class Pair<reflect out A, reflect out B>`,
         `x as Pair<String, *>` is treated like `Pair<String, Any?>`
      2. implement type data structures equivalent to what the compiler has
      3. implement isSubtypeOf checks for these data structures, like the compiler does
         * how to keep these in sync?? Tests, tests, tests!
      4. implement that isSubtypeOf check into the `is` and `as` operators. Afterwards, an `Array<String>`
         must not possibly be referenced as an `Array<S8>`
18. Function types
    1. add function types to the grammar and type system.
       * do it like Kotlin where function types are syntax sugar for `FunctionN<...>`?
         (`(A, B) -> C = emerge.core.Function2<A, B, C>`)
    2. deal with the higher-order function purity problem: do functions need to be generic on purity?
       * probably not. The compiler needs to implement parameteric side effects internally, but in the emerge language
         we can probably void that complexity. The trick is: we have the language concept of `borrow` already. If a
         function borrows a value of a function type, it HAS to invoke that function zero-or-more times during its own
         execution, and cannot possibly invoke it later. So the side-effect only needs to be tracked during the invocation
         of the higher-order function. Thus, we get a simple heuristic: 
         if a function receives a parameter that is of a function type, and that parameter is borrowed: add a hidden
         side-effect parameter to the function that is also applied to the parameter;
         e.g. `fn foo(borrow a: () -> Unit)` gets an internal representation of `E fun foo<effect E>(borrow a: E () -> Unit)`
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
19. functional-style collection operations (possible because the higher-order function purity problem is solved)
    1. start simple with forEach
    2. go on with filter, map, fold, ...
    3. more tricky: make sure the code emitted by LLVM doesn't actually do all the allocation. A chain of maps and filters
       should be compiled down to a single loop.
20. import aliases: `import emerge.platform.print as platformPrint`, `import emerge.std.HashMap as DefaultMutableMap`
21. optimize reference counting; see [](refcounting optimizations.md)
    * for this, the logic to determine where reference counts are needed must move from the LLVM backend to
      the frontend; the frontend has the tools to deal with the complexity, the backend doesn't. Especially
      temporary values are BAD offenders
22. typealiases
23. smart casts
24. fix loophole in the typesystem: the `exclusive` modifier becomes incorrect in this code:
    ```
    class Foo {}
    arr = Array.new::<exclusive Foo>(20, Foo()) // compiler doesn't complain, but should
    v: exclusive Foo = arr[0] // compiler doesn't complain here, either
    ```
    Generic code does the same without an `exclusive` type argument being written: a value of type `T` is copied
    freely, and passing an exclusive value for a parameter of type `T` doesn't end its lifetime, though `T` is
    inferred as `exclusive Foo`:
    ```
    fn g<T>(x: T) -> T = x
    fn f(x: exclusive Foo) -> exclusive Foo {
        y = g(x) // y: exclusive Foo
        return x // a second exclusive reference
    }
    fn take<T>(b: read Box<T>) -> T = b.value
    fn h(b: Box<exclusive Foo>) {
        x: const Foo = take(b)
        y: mut Foo = take(b) // the same object
    }
    ```
    Either type variables don't take `exclusive` values, or generic code treats values of type `T` as possibly
    exclusive (their lifetime ends where they are captured)
25. optional parameters
    * parameter with default value is optional
    * affects overload validation and resolution
    * default value should be evaluated on the caller side because it allows to keep the
      ABI calling conventions
      * as a consequence, only the initial declaration of a function can declare default values,
        overrides cannot
26. Declaration-Site variance
    * support declaration-site variance: `class Pair<out A, out B> { ... }`. Anticipated problems:
      * assignment to member vars that have a generic type referencing an in/out type parameter can only
        be assigned on construction -> must not be "var"
      * the code generated in the constructor for the assignment won't validate, precisely because it's
        not generally valid to assign to an out-variant/in-variant member var -> needs an exception
      * it was partially supported before; some test-cases are already present but disabled
27. named arguments
    * allow to change the order of arguments? It's important to keep the evaluation order on the
      calling side to match the order of the arguments as passed, not as declared
28. threading
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
29. review which other predefined classes should be declared `: const Any`: `String`, `ReflectionBaseType`,
    `StackTraceElement` and the boxes of the platform module (`S32Box`, ...) are never mutated after construction.
    Declaring them const changes what their fields read as and lets their values fit any mutability
30. reconsider the name `exclusive`: an `exclusive` reference promises that no other reference can mutate the object,
    not that there are no other references (`read` aliases are allowed, and a const object fits `exclusive` too).
    Look for an equally concise and expressive term that says that more precisely
31. diagnostics about the static bound of a type variable show the other type variables in it, not their values:
    `b.ordered(Bad())` with `b: Box<Num>` and `fn ordered<T : Ord<in E>>` reports `Required: read Ord<in Var(E)>`
    instead of `read Ord<in Num>`
32. a member function with type parameters of its own can't be overridden: findOverriddenFunctions compares the
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
33. parentheses in type notation, to group: `(A & B)?`. Today a nullable intersection can only be written with every
    component nullable, `A? & U?`, from which ofComponents builds `(A & U)?`; that spelling hides that the components
    get narrowed (`U?` with `U : Any?` becomes the component `U!`)
34. decorated member variables (`decorates value: T = init`) are rejected as not supported yet, as they weren't sound.
    The constructor ties the mutability of the object, `_M` in its return type `exclusive W & _M`, to that of each
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
35. `Array.trimmed` (and `String.trimmed` on top of it): copies a slice into a fresh array object of exactly the
    slice's size, so the rest of the base array can be freed. `U64.toString` returns a slice of its 21-byte buffer,
    keeping the entire buffer alive for as long as the string lives
36. various optimizations collected over time
    * static dispatch for mixed-in functions when the concrete type of the mixed-in object is known
      at compile time
37. model the frontend's rule that an intersection of disjoint classes (`N & M`, `N & Box<A>`) is below every type, as
    the bottom type it simplifies to (`BoundIntersectionTypeReference.flippedUnify`, coverage step 14): in the model,
    `Subtyping.intersection_flipped_unify` returning the carry where `is_effectively_bottom_type` holds of the
    components. It is the one entry of `OracleGrid.unify_excuses` (1049 pairs of `TypeGrid`) and the excuse of
    `closest_common_supertype_is_above_both`, and widening `GenericArguments.bottom_only` for #18 rests on it.
    Transitivity needs a lemma that what an effectively-bottom intersection accepts is below every type; the lemmas
    that take a component of an accepted intersection hold only of the other intersections then:
    `Generics.flipped_some`, `Ops.intersection_flipped_unify_found`, `Substitution.unify_into_components` and their
    ~50 call sites, and the mutability lemmas need side conditions or an exclusive assignment mutability for such
    intersections. A sibling of item 39: both make the model's unify the frontend's where they differ today
-----

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

Implementing interfaces is handy for modelling state external to the program:
_!! how to prevent race conditions in the external resource when multiple emerge threads/actors are mutating
the same atom?_

    atom StandardOut : PrintStream {
        override fn put(self: mut _, string: String) {
            // ...
        }
    }

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

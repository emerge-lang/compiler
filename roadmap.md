This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

1. ~~Refactor typechecking process~~  
   Instead of calling `validate(context)` all the time (which is not only insufficient
   but also horribly slow), create a type `BoundExpression` that is bound to a compile
   time context. It keeps all the information derived thereof; things then become easier
   with `expression.boundTo(contex).type` instead of `expression.determineType(context)`.
2. ~~InvocationExpression~~
3. ~~Operator Precedence~~
4. ~~Scope modifier PURE and READONLY~~
   nothrow will be implemented analogous later on; this is just to figure out the API
5. ~~draft of if-else expression~~
6. ~~distinguish terminating and non-terminating statements in code chunks~~
7. ~~return type checking~~
8. ~~Parser Refactoring~~
   1. ~~Execute rule on match, not on construction time for easier debugging~~
9. ~~Reportings object model for accurate detection in tests~~
10. ~~Test suite for all existing code~~
11. ~~Parser Refactoring~~
12. fallbacks: define simple logic to parse until ... when a sub-rule fails; e.g.:
     * e.g. in ParameterList: when a parameter fails, construct a dummy parameter,
     report the error, go to the next Operator.COMMA and continue
13. Generics / Templates
    * \*sigh\* this is gonna be a huuuge thing... no idea how to go about this, yet
    * ~~decide on the syntax:~~
        * Kotlin `GenericType<modifier TypeParameter>`
        * D `GenericType!TypeParameter` and `GenericType!(modifier TypeParameter)`
    * ~~Decide whether to support vararg type parameters~~ -> no
    * ~~The `readonly` and `immutable` type modifiers force `out` variance on all type parameters~~
      * Impossible, because the generic parameter can still occur in as a parameter on a readonly/pure
        member function. The compiler could do make type parameters `out` on readonly/immutable if the
        type only occurs in out locations. But if that happens automagically, adding the generic type in
        an invariant or in location becomes a breaking API change. Not good. Hence: Given a type T<E> where
        `E` only occurs in out-variant locations and the program mentions the type `(readonly|immutable) T<...>`
        then the compiler should produce a warning that the type parameter can be `out`. If the referring code
        then changes the type to `T<out ...>` the breaking-API-change problem is avoided. If the referring code
        sticks to the non-out type, its obvious that variance is not in effect.
      * consequently, if `T<out X>` only leaves member functions with `readonly self` or `immutable self` receivers
        then the compiler should warn that `T<out X>` should be referenced as `readonly T<out X>`.
14. ~~Array type~~
15. ~~Including an array literal syntax.~~ I really like Kotlins way of avoiding list/set/array literals,
    but it requires varargs. And these complicate the overload resolution EVEN more than it already is.
    So **no varargs**. The cool thing is that a concise array literal syntax can fill the role of varargs
    almost seamlessly: Kotlin `setOf(1, 2, 3)` vs this language `Set([1, 2, 3])`.
16. ~~String type, based on array~~
    * default encoding? -> unicode / utf-8?
    * string is a wrapper around an `Array<Byte>`
17. ~~Decision on compile target architecture (native/vm with pointers VS JVM)~~
    -> llvm to native, because thats interesting for me
18. ~~implement enough backend code to have a "Hello World" execute~~
19. Variable handling improvements
    * ~~decide on shadowing rules (e.g. rust does it WAY differently than Kotlin), **and implement**~~
    * ~~track assignment status of variables. It should be possible to split declaration and assignment, even on
      `val`s.~~
20. resolve any reasonably resolvable TODO in the llvm backend, including
    * ~~array deallocation, needs code in the DSL for creating loops~~ 
    * ~~reference counting - currently not done at all. Needs work in the frontend and in the backend.~~
      * no need to optimize rn, can be done later
21. sane defaults, mutability and purity
    * currently mutable and impure by default. Other languages show clearly that this is not needed. Makes sense,
      mutability and impurity are a complexity, that should only be added when needed
    * so: objects created on the stack: immutable by default
    * objects referenced from other objects: immutable by default
    * ~~function parameters: readonly be default. Functions are an API and should provide best compatibility~~
    * ~~function return types: immutable by default. Functions are an API and should provide high guarantees~~
    * ~~functions: pure by default~~
      * this is already eased by having the receiver be an explicit parameter that can get an explicit mutability
      * reading compile-time-constant data must be considered pure, too. There is no effective difference between a compile-time
        constant/literal in a function or outside of it. The type system should already enable this: global var, which
        implies immediately initialized, immutable. This could still entail reading runtime-dependent data... how to solve this?
22. ~~implement overload resolution algorithm, marked with TODOs~~
    * ~~attention: currently, when an overload doesn't match just because of mutability that is reported as "function not defined".
      while technically correct, its very negative-helpful. E.g. when assignee is `readonly` and target is `mutable` the
      error message should say something like "can't mutate ..."~~
    * ~~Also: what about overloading only based on mutabliltiy? Deny by incorporating mutability into the disjoint logic
      somehow?~~
23. object model
    1. ditch struct for class: there is no use for a struct that a `data`/`record` modifier as in Kotlin/Java couldn't
       do; especially because closed-world optimization will produce identically optimal code for a struct and a
       class with just accessors.
       1. ~~constructors: only one per class, see [partial initialization](#constructor-initialized-class-member-variables)
          and [supplemental initialization](#supplemental-initialization)~~
       2. ~~add member methods~~
       3. ~~implement visibility~~
       4. ~~allow finalizer customization~~
    2. ~~add interfaces and inheritance class impls interface~~
24. ~~move intrinsic types 100% into emerge source. Both frontend and backend should
    have the necessary toolset now to still hook in and handle them correctly~~
25. ~~implement weak references~~
26. Index operator `obj[index]` to `operator fun get(index)` and `operator fun set(index)`
    1. ~~index access can always throw IndexOutOfBounds; work out a nothrow alternative. Maybe `.safeGet(index)` returning `Either`?~~
27. Stdlib _absolute_ Basics
    * arithmetic
        * ~~overflow-safe implementations of the actual operators + - * ...~~
        * overflow-unsafe intrinsics, e.g. `emerge.std.math.addWithOverflow(a: i32, b: i32)`
        * ~~conversions between the integral types, especially handy for word~~
    * ~~array bounds checks, null deref~~
    * ~~a to-string abstraction: Java-style toString on all objects is probably overkill, more like rusts Display trait~~
    * equality
      * ~~reference equality operator: really === ??~~ -> reference equality is not supported as it introduces inherent impurity
      * ~~it would be great to be able to do == on Any~~ without reference equality to fall back on, there is no sane default
28. ~~while + do-while loops~~
29. error handling
    1. this is going to touch the runtime significantly. Use this opportunity to
        1. ~~find out what all the gnu gcc runtime libs do, which and why they're needed~~
        2. ~~bundle the ones for x86_64 into the compiler, so they're available wherever the compiler can run~~
        3. ~~implement some method for using an LLVM installation on windows, so windows -> linux cross-compilation is possible~~
    2. `throw` statement
        1. ~~implement Printable on exceptions so the toplevel main() function can show them properly~~
        2. ~~actual throw expression~~
        3. ~~cleanup on unwind/exception propagation~~
    3. ~~`Throwable` for everything that can be thrown, `Exception : Throwable` for recoverable errors,
       `Error : Throwable` for unrecoverable errors. `Error` cannot be `catch`ed~~
    4. ~~try+catch+finally~~
30. add instance-of and cast operations
31. implement module dependencies and access checks
    1. upgrade the compilers CLI interface to a configuration via a proper config format. NOT YAML! Maybe TOML, maybe PKL. Should have schema
    2. implement dependencies between input modules/source sets
        * stdlib depends on platform module provided by backend
        * modules only have access to things in other modules that they explicitly depend on
32. extend OO model
    1. class extends class will not be a thing! composition all the way. Probably needs some boilerplate-reduction
       tools, like Kotlins `by`, but more powerful
    2. add accessor-based member variables to interfaces
    3. review the vtable approach: does looking for a prefix suffice to keep them small?
        * idea 1: put 1s into the bitwise hashes at different, non-harmonic frequencies to generate hard-to-clash patterns
            * maybe adding phase-shift helps even more
            * e.g. '10101010101010...', '100100100100100100', '1000100010001000'
        * if that isn't enough, it could make sense to include both a left- and a right shift, so any unique
          sequence from the hashes can be chosen, not just prefixes.
        * TEST, TEST, TEST. Unit test the shit out of the algorithm. More to proof the concept, less to
          test the implementation.
    4. deal with the wrapper mutability problem: do types need to be generic on mutability?
    5. add `sealed` interfaces as in Kotlin
    6. algebraic data types
       1. union type: `TypeA | TypeB | TypeC`
       2. conjunction type: `TypeA & TypeB & TypeC`
33. general iterable types
    * implement generic supertypes - yey, another logic monstrosity
    * Like Java Iterable<T>, D ranges, ... ?
    * for each over iterable
34. arrays slices; goal/target situation
    * there are array-base-objects, identical to what an Array<T> is before
    * emerge source can never reference these base objects directly, only ever slices of that
    * when emerge source says "Array<T>", this is actually a fat pointer consisting of
      * a pointer to the base array object that holds reference count, vtable, the length of the memory chunk
        and the actual array data
      * a pointer to the first element in the slice
      * the length of the slice
    * so when you have a variable/parameter of type `Array<T>`, it can be a full array, but could also just be
      a sub-slice of one
    * `Array.new<T>(UWord, T)` creates a base array object and then returns a slice covering the entire array
    * slicing functions, e.g. `someArray[1..5]`
    * how to deal with `exclusive` mutability? idea: Array.new is the only way to get hold of an `exclusive`
      slice. Slicing operations always capture the old slice, stopping the exclusive lifetime and settling the
      sub-slice to either `mut` or `const`
    * apply to standard library, especially IO functions
35. for each loops over arrays
    ```
    for each item in iterable { /* ... */ }
    // is actually
    val temp1 = iterable.iterator() // or whatever was decided in step 19
    while temp1.hasNext() {
        val item = temp1.next()
        /* ... */
    }
    
    for each i in 0 .. 10 { /* ... */ }
    // gets rewritten to
    for i in 0.rangeTo(10) { /* ... */ }
    ```
36. Stdlib basics
    * some good standard collections
    * ArrayList, LinkedList, (De)Queue, Stack, ...
      * hashCodes: Java-style is overkill, have an explicit Hashable interface
    * Map
    * string templates
      * interpolation like in Kotlin instead of concatenation like in Java or D
      * make that work with the Printable interface. So e.g. a template "a ${x} b ${y} c" desugars to an
        memory-buffered printstream, with calls to put of "a ", x.printTo(...), " b ", y.printTo(...), " c"
    * remote print and println functions and instead expose the emerge.platform.StandardOut and StandardError
      variables
      * add emerge.platform.StandardIn for good measure
37. ALPHA TESTABLE MILESTONE; At this point, the language should be powerful enough to tackle advent of code challenges.
    Todo: actually try and solve some!
38. integration tests!! Include emerge source code in this repository that tests the runtime and correct compilation.
    The unit tests in the frontend test the negative cases; these should test the positive ones. E.g. that 2+3=5,
    refcounting, control flow + exceptions, ...
39. documentation and presentation
    * from a user perspective. Github pages?
      * language syntax and semantics, maybe a good tutorial
      * design decisions, philosophy and reasoning
    * from a maintainer perspective
      * compiler architecture
      * llvm patterns
      * debugging techniques
40. user tooling
    * installable packages that handle upgrades/multiple parallel versions, too
      * windows
      * debian
    * CLI interface for the compiler
    * language server and VSCode plugin
41. Function types
    1. `operator fun invoke`: `obj(param)` to `obj.invoke(param)`
    2. Regular functions: `(T1, T2) -> R`
    3. do we need functions with receiver? Or is receiver/self VS regular parameter just a syntax
       thing on the declaration side?
    4. deal with the higher-order function purity problem: do functions need to be generic on purity?
    5. extend InvocationExpression
    6. implement `objectRef.foo()` where `foo` is a property of a function type
42. functional-style collection operations (possible because the higher-order function purity problem is solved)
    1. start simple with forEach
    2. go on with filter, map, fold, ...
    3. more tricky: make sure the code emitted by LLVM doesn't actually do all the allocation. A chain of maps and filters
       should be compiled down to a single loop.
43. import aliases: `import emerge.platform.print as platformPrint`, `import emerge.std.HashMap as DefaultMutableMap`
44. optimize reference counting; see [](refcounting optimizations.md)
    * for this, the logic to determine where reference counts are needed must move from the LLVM backend to
      the frontend; the frontend has the tools to deal with the complexity, the backend doesn't. Especially
      temporary values are BAD offenders
45. some stdlib primitives for filesystem IO
46. typealiases
47. smart casts
48. fix loophole in the typesystem: the `exclusive` modifier becomes incorrect in this code:
    ```
    class Foo {}
    arr = Array.new::<exclusive Foo>(20, Foo()) // compiler doesn't complain, but should
    v: exclusive Foo = arr[0] // compiler doesn't complain here, either
    ```
49. optional parameters
    * parameter with default value is optional
    * affects overload validation and resolution
    * default value should be evaluated on the caller side because it allows to keep the
      ABI calling conventions
      * as a consequence, only the initial declaration of a function can declare default values,
        overrides cannot
50. named arguments
    * allow to change the order of arguments? Its important to keep the evaluation order on the
      calling side to match the order of the arguments as passed, not as declared
51. threading
    The whole shtick of the explicit-mutability types is to simplify multithreading. Avoiding the
    complexity of having a `shared` mutability like D allows to infer some properties necessary for
    multithreading:
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
      Or should lambda literals that capture references have `readout` mutability to prevent them from being
      sent across threads? This is important to get a decent WorkerThread/ForkJoinPool API.
    * On the matter of ForkJoin/WorkerThread: this would necessitate a Futures API:
      ```
      val futureVal: Future<S32> = forkJoinPool.submit({ doExpensiveComputation() })
      ```
      Which brings the important question to the table: Push-Based or Pull-Based futures?

-----

## Future features

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

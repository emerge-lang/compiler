This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

1. add instance-of and cast operations
2. implement module dependencies and access checks
   1. upgrade the compilers CLI interface to a configuration via a proper config format. NOT YAML! Maybe TOML, maybe PKL. Should have schema
   2. implement dependencies between input modules/source sets
       * stdlib depends on platform module provided by backend
       * modules only have access to things in other modules that they explicitly depend on
3. extend OO model
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
4. general iterable types
   * implement generic supertypes - yey, another logic monstrosity
   * Like Java Iterable<T>, D ranges, ... ?
   * for each over iterable
5. arrays slices; goal/target situation
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
6. for each loops over arrays
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
7. Stdlib basics
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
8. ALPHA TESTABLE MILESTONE; At this point, the language should be powerful enough to tackle advent of code challenges.
   Todo: actually try and solve some!
9. integration tests!! Include emerge source code in this repository that tests the runtime and correct compilation.
   The unit tests in the frontend test the negative cases; these should test the positive ones. E.g. that 2+3=5,
   refcounting, control flow + exceptions, ...
10. documentation and presentation
    * from a user perspective. Github pages?
      * language syntax and semantics, maybe a good tutorial
      * design decisions, philosophy and reasoning
    * from a maintainer perspective
      * compiler architecture
      * llvm patterns
      * debugging techniques
11. user tooling
    * installable packages that handle upgrades/multiple parallel versions, too
      * windows
      * debian
    * CLI interface for the compiler
    * language server and VSCode plugin
12. Function types
    1. `operator fun invoke`: `obj(param)` to `obj.invoke(param)`
    2. Regular functions: `(T1, T2) -> R`
    3. do we need functions with receiver? Or is receiver/self VS regular parameter just a syntax
       thing on the declaration side?
    4. deal with the higher-order function purity problem: do functions need to be generic on purity?
    5. extend InvocationExpression
    6. implement `objectRef.foo()` where `foo` is a property of a function type
13. functional-style collection operations (possible because the higher-order function purity problem is solved)
    1. start simple with forEach
    2. go on with filter, map, fold, ...
    3. more tricky: make sure the code emitted by LLVM doesn't actually do all the allocation. A chain of maps and filters
       should be compiled down to a single loop.
14. import aliases: `import emerge.platform.print as platformPrint`, `import emerge.std.HashMap as DefaultMutableMap`
15. optimize reference counting; see [](refcounting optimizations.md)
    * for this, the logic to determine where reference counts are needed must move from the LLVM backend to
      the frontend; the frontend has the tools to deal with the complexity, the backend doesn't. Especially
      temporary values are BAD offenders
16. some stdlib primitives for filesystem IO
17. typealiases
18. smart casts
19. fix loophole in the typesystem: the `exclusive` modifier becomes incorrect in this code:
    ```
    class Foo {}
    arr = Array.new::<exclusive Foo>(20, Foo()) // compiler doesn't complain, but should
    v: exclusive Foo = arr[0] // compiler doesn't complain here, either
    ```
20. optional parameters
    * parameter with default value is optional
    * affects overload validation and resolution
    * default value should be evaluated on the caller side because it allows to keep the
      ABI calling conventions
      * as a consequence, only the initial declaration of a function can declare default values,
        overrides cannot
21. named arguments
    * allow to change the order of arguments? Its important to keep the evaluation order on the
      calling side to match the order of the arguments as passed, not as declared
22. threading
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

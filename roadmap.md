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
9. Reportings object model for accurate detection in tests
10. Test suite for all existing code
11. Parser Refactoring
   2. fallbacks: define simple logic to parse until ... when a sub-rule fails; e.g.:
     * e.g. in ParameterList: when a parameter fails, construct a dummy parameter,
       report the error, go to the next Operator.COMMA and continue
12. object model
    1. class definition
    2. struct definition
    3. reference counting vs garbage collection
13. extend InvocationExeption
    1. handle constructors
    2. when checking `objRef.method()` error if `method` is a property  
      (will be implemented with function types later on)
14. exceptions
    1. `throw` statement
    2. NOTHROW scope modifier
    3. try+catch+finally
15. Generics / Templates
    * \*sigh\* this is gonna be a huuuge thing... no idea how to go about this, yet
    * decide on the syntax:
      * Kotlin `GenericType<modifier TypeParameter>`
      * D `GenericType!TypeParameter` and `GenericType!(modifier TypeParameter)`
    * Decide whether to support vararg type parameters
    * The `readonly` and `immutable` type modifiers force `out` variance on all type parameters
16. Stdlib Collections
    * Iterables: java.util.Iterable, D Ranges or sth. else?
17. All operator overloads, including
    * contains(T): Boolean
    * <E : Iterable> rangeTo(T): E
18. Decision on compile target architecture (native/vm with pointers VS JVM)
19. Array type
20. Index operator `obj[index]` to `operator fun get(index)` and `operator fun set(index)`
21. for each control structure:
    ```
    for each item in iterable { /* ... */ }
    // is actually
    val temp1 = iterable.iterator() // or whatever was decided in steps 15 and 16
    while temp1.hasNext() {
      val item = temp1.next()
      /* ... */
    }

    for each i in 0 .. 10 { /* ... */ }
    // gets rewritten to
    for i in 0.rangeTo(10) { /* ... */ }
    ```
22. while / do-while
23. Jump targets for return, break and continue like in Kotlin
24. Typealiases
25. Strings + String literals
    * i ABSOLUTELY want `typealias String = immutable Array<Char>`
26. Function types
    1. `operator fun invoke`: `obj(param)` to `obj.invoke(param)`
    2. Regular functions: `(T1, T2) -> R`
    3. Functions w/ receiver: `O.(T1, T2) -> R` that can be invoked on objects
       as if they were extension functions:
       ```
       val fn: O.(T1, T2) -> R = ...
       val obj: O = ...
       obj.fn(param1, param2)
       ```
27. CTFE
28. smart casts
29. deferred statements
    * `scope(exit) {stmt}`, `scope(success) {stmt}` and `scope(fail) {stmt}`
30. ...


-----

Small things to think about:

* Function parameters that the function may not alter are declared as `readonly` and `immutable` with the
  exception of the receiver paramter: it can be declared readonly by declaring the function as `selector`:
  `struct X { selector fun foo() -> Unit }` in dotlin equals `struct X { void foo() const }` in D
  See [this software engineering SE question](https://softwareengineering.stackexchange.com/questions/348113/opposite-of-mutating)
This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

1. Refactor typechecking process  
   Instead of calling `validate(context)` all the time (which is not only insufficient
   but also horribly slow), create a type `BoundExpression` that is bound to a compile
   time context. It keeps all the information derived thereof; things then become easier
   with `expression.boundTo(contex).type` instead of `expression.determineType(context)`.
1. InvocationExpression
2. Scope modifier PURE  
   nothrow will be implemented analogous later on; this is just to figure out the API
3. distinguish terminating and non-terminating statements in code chunks
4. return type checking
5. Parsing fallbacks: define simple logic to parse until ... when a sub-rule fails; e.g.:
   * in ParameterList: when a parameter fails, construct a dummy parameter,
     report the error, go to the next Operator.COMMA and continue
5. Test suite for all existing code
6. control structures
7. object model
   1. class definition
   2. struct definition
8. extend InvocationExeption
   1. handle constructors
   2. when checking `objRef.method()` error if `method` is a property  
      (will be implemented with function types later on)
9. exceptions
   1. `throw` statement
   2. NOTHROW scope modifier
   3. try+catch+finally
10. Generics / Templates
    * \*sigh\* this is gonna be a huuuge thing... no idea how to go about this, yet
    * decide on the syntax:
      * Kotlin `GenericType<modifier TypeParameter>`
      * D `GenericType!TypeParameter` and `GenericType!(modifier TypeParameter)`
    * Decide whether to support vararg type parameters
      * are needed if we want to avoid to shit like `Function1<R, T1>, Function2<R, T1, T2> ... Function10<R, T1 ... T10>`
      * would be easier with templates
11. Decision on compile target architecture (native/vm with pointers VS JVM)
12. Array type
13. Index operator `obj[index]` to `operator fun get(index)` and `operator fun set(index)`
14. Typealiases
15. Strings + String literals
    * i ABSOLUTELY want `typealias String = immutable Array<Char>`
16. Function types
    1. `operator fun invoke`
    2. Syntax-Sugar for function type literals:
       * `(T1, T2) -> R` to `Function<R, T1, T2>` 
    4. what about function types with receiver? needed for builders :/ :/
       * would yield syntax sugar `O.(T1, T2) -> R` to `Function<O, R, T1, T2>` 
17. CTFE 
18. smart casts
19. deferred statements
    * `scope(exit) {stmt}`, `scope(success) {stmt}` and `scope(fail) {stmt}`
20. ...
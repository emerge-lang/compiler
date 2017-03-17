This file describes the Items that are next on the TODO list. **This list is NOT EXHAUSTIVE!**

1. InvocationExpression
   1. since objects & properties are not implemented yet, resolve only basetype functions
      and extension functions
2. Scope modifier PURE  
   nothrow will be implemented analogous later on; this is just to figure out the API
3. distinguish terminating and non-terminating statements in code chunks
4. return type checking
5. Test suite for all existing code
6. control structures
7. object model
   1. class definition
8. extend InvocationExeption
   1. handle constructors
   2. handle the ambigous case `objRef.method()` where method can be one of:
      * function defined on the type of `objRef`
      * extension function defined on the type of `objRef`
      * error if `method` is a property (will be implemented with function types later on)
9. exceptions
   1. `throw` statement
   2. NOTHROW scope modifier
   3. try+catch+finally
10. Generics / Templates
    * \*sigh\* this is gonna be a huuuge thing... no idea how to go about this, yet
11. Function types
    1. `operator fun invoke`
    2. Syntax-Sugar for function type literals:
       * `(T1, T2) -> R` to `Function<Unit, R, T1, T2>`
    3. what about function types with receiver? needed for builders :/ :/
12. CTFE 
13. ...
14. smart casts
15. deferred statements
    * `scope(exit) {stmt}`, `scope(success) {stmt}` and `scope(fail) {stmt}`
16. ...
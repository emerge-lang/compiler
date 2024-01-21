# My Dream Language

* influenced by: Kotlin, D, Rust, Groovy, TypeScript, Java, Jai, PHP

## Separating Software

In Emerge, software is split up into modules. Every file is one module can contain an
arbitrary number of declarations. The name of a module is derived from its relativ path
to its source root:

    src/
        moduleOne.dt
          declaration Foo
          declaration Bar
        moduleTwo.dt
          declaration FooBar
      
Results in two modules `moduleOne` and `moduleTwo` declaring these symbols:
 
* `moduleOne.Foo`
* `moduleOne.Bar`
* `moduleTwo.FooBar`

---

Every file must have a `module` statement at the very top. That must match the module
name derived from the directory structure. The purpose of this is not to assist the
 compiler (since it can unambiguously derive the name) but to support programmers;
 i assume it is easier to hit `Ctrl + Home` and read that line than to look through the
 directory structure; especially outside of an IDE.
 
In the file `src/package/module1.dt` these contents produce distinct results:

```
    module package.module1
    
    fun XY() = 3 // FQN = package.module1.XY 
    
    // -> compiles
```
```
    module package.someOtherModule
    
    // ERROR: module declration in file does not match file location
```
```
    fun XY() = 3

    module package.module1
    
    // ERROR: module declaration must be the first statement in a file
```

---

Directory names contribute to the module name as well:

    src/
        package/
            moduleOne.dt
              declaration FooBar
          
Results in a module `package.moduleOne` declaring the symbol `package.moduleOne.FooBar`

---

Multiple modules can be grouped to a package. This is creating a file with the name
`package.dt` within the directory that contains all the modules that are to be included.  
Within that file, all the included modules are referenced using a `public import`:

```
    src/
        package/
            package.dt
            moduleOne.dt
              declaration Foo
              declaration Bar
            moduleTwo.dt
              declaration FooBar
```
```
// package.dt
public import moduleTwo.*
public import moduleOne.Foo
```

Results in these symbols being defined

    package.moduleOne.Foo
    package.moduleOne.Bar
    package.moduleTwo.FooBar
    package
    
When other modules import from `package`, the names are attempted to be resolved
 within all the publicly imported modules:
 
* `import package.Foo` resolves to FQN `package.moduleOne.Foo`
* `import package.Foobar` resolves to FQN `package.moduleTwo.FooBar`
* `import package.Bar` errors, because `package.moduleOne.Bar` is not a public import of
  the package
  
---

Source roots may not contain a file named `package.dt`:

    src/
        package.dt // ERROR
        subdir/
            package.dt // OK

Files named `package.dt` may contain only public imports.

## Basics

    // single line comment
    /* multi-line comment */
    /// single-line doc comment
    /**
     * multiline doc comment
     */

One statement per line. `;` only used to separate multiple statements on one line. Lines ending with a `;` (and possible trailing whitespace) are an error

## Type System

* Statically typed
* All types first-class citizens as in Kotlin and Scala, no native/non-native differentiation
* Function-Types
* `Any` and `Unit` instead of `void`

### Reasoning about mutability

#### Type mutabilities (inpsired from D)

* no modifier => readonly
* mutable
* immutable
* for composite types can be specified granularly: `mutable Array<readonly Foo>`

Those are transitive as in D; see below for variable declaration and aissgnments to variables.

Values of modified Types can be converterted to an other type according to this table. The letfomst column shows the source type, the headings show the target type.

| \-          |  T  | readonly T | immutable T |
| ----------- | :-: | ---------- | ----------- |
| T           |  Y  | Y          | N           |
| readonly T  |  N  | Y          | N           |
| immutable T |  N  | Y          | Y           |

##### Syntax

Mutability modifiers can be prefixed to variable declarations to apply the
mutability to the inferred type (see below).

When declaring types elsewhere, these rules apply:

Prefixing a type with a modifier modifies the type:

    readonly Any
    
In case of generics, a modifier applies to the parameterised type as 
well as to all of the type paremeters:

    readonly Array<Any>
    // is equal to
    readonly Array<readonly Any>
    
If Type parameters need to have different type modifiers, those can 
be specified. They act the same

    readonly Array<mutable Any>
    
    readonly Array<mutable Set<Any>> // Any is mutable Any
    
    readonly Array<mutable Set<readonly Any>>

#### Void-Safety (from Kotlin)

Types are non-nullable by default. Postfix `?` denotes a nullable type. Postfix `!!` converts a nullable
expression to a non-nullable one, throwing a `NullValueException` if the value is null.

### Type inference

Type inference as in Kotlin (or as in D with auto).

    var a = 5 // a is of type Int as inferred from the assigned value
    a = "Foo" // Error: a is of type Int, cannot assign String (String is not a subtype of Int)


### Variable Declaration

As in Kotlin, Variables are introduced with `val` and `val`. `var` Variables can be reassigned, `val` ones cannot.

    val a = 5
	a = 3 // Error: Cannot reassign val a

	var b = "Foo"
    b = "Hello" // OK

Type modifiers can be written before the `var` and `val` keyword. That is syntax sugar that assures the modifier on the variable type. Note that, however, a `var` of type `immutable X` can be assigned new values, as long as
those are `immutable`, too.

    readonly var a = 3 // is equal to
    var a: readonly Int = 3

    reaonly var foo: Int = 3 // is equal to
    var foo: readonly Int = 3

    readonly var a = 5
    var b = a
    b = 3 // OK
    a = b // error, cannot convert Int to readonly(Int)

    immutable a = 5
    b = a
    b = 3 // OK
    a = 3 // error, a is immutable

### Functions can be Values; Function Type Syntax

Functions can be Values, such as Ints and Strings. Function Types are denoted as in Kotlin

    (Type, Type) -> ReturnType

Function literals are denoted likewise:

    (paramName: Type, paramName: Type) -> ReturnType {
        // code...
    }

As in Kotlin, the `=` character can be used to denote single line functions. It cannot be used for `Unit` functions

    (paramName: Type) -> ReturnType = expression

    (paramName: Type) -> Unit = expression // Error
    (paramName: Type) -> Unit { expression } // OK

For those single-line function literals, the return type can be omitted and inferred from the expression:

    (paramName: Type) = expression

If function literals are used in a context where their type is already constrainted, the types of the parameters can be omitted:

    somFunc: (Type) -> ReturnType = (foo) = bar 

Note that curly braces alone do not denote a function literal.

    a: () -> Unit = { doSth() } // This would expect doSth() to return a () -> Unit and assign it to a; see nested scopes below
    a: () -> Unit = () { doSth() } // OK

#### Overloading functions

If functions were *only* values, overloads would be impossible. But because overloads are an important feature,
Emerge supports functions and methods in the sense as used in Kotlin and Java:

    fun someFunction(paramName: ParamType) -> ReturnType = expression

    fun someFunction(paramNameOverloaded: ParamTypeOverloaded) -> ReturnType = expression

#### Parameter modifiers

All parameters to a function are `val`; that cannot be changed. The `readonly` and `immutable` modifiers can be 
added where needed. They behave just like on variables:

    fun someFun(valParam: Type) { }

    fun someFun(readonly valParam: Type) {} // this is actually treated as 
    fun someFun(valParam: readonly Type) {}
	
On Lambdas / typeless function literals this comes in handy:

    val a: (Int) -> Int = (readonly a) -> a + 3

## More Syntax

The general syntax is a mix of Kotlin and D, with some syntax-sugar from groovy.

### Control Structures return values

    a = try {
		doSomethingRiskyAndReturnAValue()
    }
    catch(error: Throwable) {
        // handle; return a value from here or quit the scope
    }

    a = if (foo) 3 else 5 // no ternary operator

### Safe access operator

Nullable fields of data structures can safely be traversed with the `?.` operator:

	someObj: SomeType = ...
    a: String? = someObj.someValue?.someString

If any of the fields postfixed with `?.` are null, the entire expression becomes nullable.

Likewise, elements can be postfixed with `!!`; the expression stays non-nullable but may throw:

    someObj: SomeType = ...
    a: String = someObj.someValue!!.someString

### Elvis Operator

    a = nullableExpression ?: nonNullableExpression
    b = nullableExpression ?: throw Exception()

### Nested scopes via lambdas

Anywhere, a nested scope can be opened:

    a = 5
    b = 5
    { 
        c = 5
    }

As per Kotlin syntax, this would be a lambda. But in our language, it is not yet a fully qualified function literal, so ite becomes a nested scope. The nested scope does not have access to the outer scope. It may return 
a value to the outer scope:

    a = {
      // do some computation
      return value
    }

To access the outer scope, the variables need to be explicitly listed:

    a = 5
    b = 3
    c = "Foobar"

    (a, c) {
       // do sth.
    }

This is so that the syntax supports the maturing of a piece of code from being somewhere inlined in a function to possibly becoming a public API, as Jonathan Blow points out in one of his videos regarding his language Jai.

	fun outerScope() {
		// some code
	}


	fun outerScope() {
    	c = {
    	    // some code
	    }
	}

	fun outerScope() {
	    c = (a, b) {
    	    // some code
	    }
	}


    fun outerScope() {
    	fun nestedFun(a: Int, b: Int) -> Int {
			// some code
    	}

		c = nestedFun(a, b)
	}

	fun toplevelFun(a: Int, b: Int) -> Int {
		// some code
    }
    
### Operator Precedence

This section defines operator precedence. All operators on one line have an equal precedence
and are evaluated left to right.  
The operators are listed with descending precedence.

```
. ?.
!! []
* /
+ -
== > < >= <= === !==
as as?
?:
```

## Function modifiers

As D has, our language has function modifiers that restrict its behaviour. These modifiers are transitive, too, as in D. 

* `pure`: Same input => same output. This implies that the function does not read or write any global state and that it does not call *impure* functions (functions not modified with `pure`). This is targeted to CTFE.
* `readonly`: Denotes that the function does not modify the object or struct instance it is declared upon. Within such functions, the `this` reference becomes `readonly` (thus preventing modification of the object).
* `immutable`: Same as `readonly`
* `nothrow`: The function must not throw exceptions. If it invokes functions that are not modified with `nothrow`, the exceptions must be caught.

The type modifiers are written *before* the function declaration (as opposed to after in D):

	pure fun foo(param: String) -> Int = param.length


	foo = pure (param: String) -> Int = param.length

    
    fun outerScope() {
    	pure (a, b) {
    	}
    }


    fun outerScope() {
        pure {}
    }    

## Data structures

Emerge has classes, interfaces and structs. The syntax is more traditional like in D or Java (and less like in Kotlin). The constructor notation of TypeScript is used:

    class MyClass : BaseClass, ImplementedInterface {
    	constructor(arg1: Type) {
            super(arg1)
        }
    }

Like in D, the call to `super` need not be the first statement in the constructor. Code before the `super` invocation is treated as if there was no class context.

    class MyClass : BaseClass, ImplementedInterface {
        readonly functionTypeFieldWithoutOverloads = (param1: Type) -> ReturnType = expression

        fun overloadableFunction(param1: Type) -> ReturnType = expression
        fun overloadableFunction(param1: AnotherType) -> ReturnType = expression

        readonly fun constMethod(param1: Type) -> ReturnType 
    }

Since type/function modifiers are transitive, only `constMethod` can be invoked on readonly or immutable references to instances of the class:

    mutRef = MyClass()
    readonly roRef = mutRef

    mutRef.constMethod(param) // OK
    mutRef.overloadableFunction(param) // OK

    roRef.constMethod(param) // OK
    roRef.overloadableFunction(param) // Error: Cannot invoke mutable function MyClass#overloadableFunction on readonly reference roRef

	mutRef.functionTypeFieldWithoutOverloads(param) // OK
	
	a = roRef.functionTypeFieldWithoutOverloads // OK, NO INVOCATION!!

    a() // Error: Cannot invoke mutable function which references readonly state
	roRef.functionTypeFieldWithoutOverloads() // Error: Cannot invoke mutable function which references readonly state

The function literal in the function type field can be declared `readonly`. It now only has `readonly` access to the class scope and thus can be invoked on a `readonly` reference:

    class MyClass {
        fnTypeField = readonly(param1: Type) -> ReturnType = expression
    }

    readonly obj = MyClass()
    obj.fnTypeField(param) // OK

Note that the `readonly` modifier of the class field does not affect the function value. This modifier would only mean that the field cannot be changed:

    class MyClass {
        readonly fnTypeField = () -> Unit { doSth() } 
    }

    obj = MyClass()
    
    fnVar: () -> Unit = obj.fnTypeField // OK
    fnVar() // OK
    
	obj.fnTypeField = () { doSthElse() } // Error: Cannot assign value to readonly variable obj.fnTypeField

### Visibility  Modifiers

Emerge distinguishes between visibility within the same source set/libary
and outside code. Elements can be visible throughout an entire codebase but not
to code that lives in other code bases. The goal of this is to enable more 
optimization: this distinction reduces the number of symbols exposed to other
code (e.g. in a dll/so). That means less ABI contracts have to be upheld. The code
that need not comply to an ABI contract can be further optimized, violating the
ABI contract. An example case: There is an interface in the application that
is visible to all other code in the application but not to outside code. When
there is only one implementation for this interface in the codebase, the compiler
can treat the code as if the interface does not exist and the implementation was
declared as final (no subclasses allowed).

|Modifier   | Visibility                       | | | | 
|-----------|-----------|------------|--------|------|
|           |same module|same package|codebase|global|
|`private`  |     Y     |     N      |   N    |   N  |
|`protected`|     Y     |     Y      |   N    |   N  |
|`internal` |     Y     |     Y      |   Y    |   N  |
|`export`   |     Y     |     Y      |   Y    |   Y  |

If a modifier is omitted, the visibility defaults to `internal`.

The modifier `protected` can be further qualified (see the `package` modifier in D) by
putting a package name in parenthesis after tha modifier. That denotes the visibility boundary. For example:

Assume the following package and module structure:

    com.myapp
        main
        foo/
            moduleA
        bar/
            moduleB
      
The following table shows the semantics of the qualified visibility modifier as
if used within `moduleA`:

|Modifier                  | Visibility                                           |
|--------------------------|------------------------------------------------------|
|`protected`               | All code inside com/myapp/foo                        |
|`protected(com.myapp.foo)`| All code inside com/myapp/foo                        |
|`protected(com.myapp)`    | All code inside com/myapp, including the bar package |
                  
---

Although applicable, `public` was deliberately not used. This avoids conflicts between
the semantics users might know from other languages. E.g. public in Kotlin/Java means
something else than in D. This wording does not collide with any of the languages this
one draws inspiration from.


### Interfaces + abstract Classes

They work just the same way they do in any OOP language. Default implementations on interfaces are supported.

As in Kotlin, interfaces and abstract classes can defined abstract fields:

    interface IntfA {
        abstract foo: Int
    }

    abstract class AbstrCls {
        abstract foo: String
    }

### Structs

Data classes from Kotlin are not supported. However, structs from D are supported. While they might not offer any benefit in a JVM backend, they might very well do so on a LLVM backend.

    struct Foo {
        member: Int
    }

Struct constructors work as in D. Because Emerge does not know the `new` keyword, there is no syntactical difference in instatiating a class or a struct. However, as in D, the memory layout of a struct must be known at
compile time.

    struct Foo {
        member: Int

        constructor(member: Int) {} // Error: Structs cannot have constructors
    }

To resolve this, the same principle as in D applies, put to life with kotlin syntax:

    struct Foo {
        member: Int
        
        private constructor; // notice the missing () and {}

        static operator fun invoke(member: String) = Foo(Int.parseInt(member)) // OK
    }

    a = Foo(4) // Error: Constructor of Foo is private
    a = Foo("4") // OK, calls Foo.invoke("4")
    

### Inheritance

Structs have no inheritance.

A class can only inherit one other class. A class can implement as many Interfaces as desired. Conflicts are resolved as in Kotlin:

    interface IntfA {
        fun someMethod() -> Unit {
        }
    }

    interface IntfB {
        fun someMethod() -> Unit {
        }
    }


    class MyClass : IntfA, IntfB {}
    // Error: Conflictin inherited method implementations IntfA#someMethod and IntfB#someMethod

    
    class MyClass : IntfA, IntfB {
        override fun someMethod() -> Unit {
            IntfA.this.someMethod()
        }
    }
	// OK

As in Kotlin, overriden methods must be marked with the `override` modifier.


### Delegation / Decorators

The `alias this` syntax from D is deliberately not used. Instead, a syntax closer to trait imports in PHP is used.

Within a wrapper/decorator class:

    // expose ALL methods and fields from member variable nested:
    expose * of nested

    // expose only the foo method of member variable nested:
    expose { foo } of nested

    // expose the foo method with a different name
    expose { foo as foo2, sthElse } of nested

The declared field must not be nullable:

    class Wrapper {
        private nestedA: Type
        private nestedB: Type?
 
        expose * of nestedA // OK
        expose * of nestedB // Error: Cannot expose members of nullable field
    }

### Operator overloading

Operators can be overridden from within a data structure and using extension
methods:

    class foo {
        operator fun opPlus(other: foo) -> foo
    }
    
    operator fun foo.opMinus(other: foo) -> foo
    
    val foo1 = foo()
    val foo2 = foo()
    
    val a = foo1 + foo2         // is rewritten to
        a = foo1.opPlus(foo2)   // using dynamic dispatch 
        
    val b = foo1 - foo2         // is rewritten to
        b = foo1.opMius(foo2)   // which is semantically equal to
        b = opMinus(foo1, foo2) // and uses static dispatch
        
Combined operate and assign can be overloaded separately:

    class foo {
        operator fun opPlus(other: foo) -> foo
        operator fun opPlusAssign(other: foo)
    }
    
    val foo1 = foo()
    val foo2 = foo()
    
    val a = foo1 + foo2 // invokes foo1.opPlus
    foo2 += foo1 // is rewritten to
    foo2.opPlusAssign(foo1)
        
#### Binary operators

All binary operator functions must take exactly 1 parameter. The type of that
parameter can vary; dispatch is done as if the operator function was
invoked directly.

    struct foo {
        operator fun opPlus(other: foo) -> foo
        operator fun opPlus(other: Int) -> foo
    }

    val foo = foo()
    val a = foo + foo() // invokes foo#opPlus(foo)
    val b = foo + 3     // invokes foo#opPlus(Int)
   
Operator overloads for simple operators have to be readonly; overloads
for combined operation and assignment must return `Unit` and need not be
readonly.
  
Operator functions do not need to be marked as readonly. It would be more
clean and explicit but would also introduce a lot of noise when a type
overrides lots of operators.

These binary operators can be overloaded:

|Operator|Function Name      |readonly?|source   |is rewritten to           |
|--------|-------------------|---------|---------|--------------------------|
|+       |opPlus             |yes      |`a + b`  |`a.opPlus(b)`             |
|-       |opMinus            |yes      |`a - b`  |`a.opMinus(b)`            |
|*       |opTimes            |yes      |`a * b`  |`a.opTimes(b)`            |
|/       |opDivide           |yes      |`a / b`  |`a.opDivide(b)`           |
|%       |opModulo           |yes      |`a % b`  |`a.opModulo(b)`           |
|..      |rangeTo            |yes      |`a..b`   |`a.rangeTo(b)`            |
|in      |contains           |yes      |`a in b` |`a.contains(b)`           |
|>       |opCompare          |yes      |`a > b`  |`a.compareTo(b) >  0`     |
|>=      |opCompare          |yes      |`a >= b` |`a.compareTo(b) >= 0`     |
|<       |opCompare          |yes      |`a < b`  |`a.compareTo(b) <  0`     |
|<=      |opCompare          |yes      |`a <= b` |`a.compareTo(b) <= 0`     |
|&       |opAnd              |yes      |`a & b`  |`a.opAnd(b)`              |
|\|      |opOr               |yes      |`a | b`  |`a.opOr(b)`               |
|^       |opXor              |yes      |`a ^ b`  |`a.opXor(b)`              |
|>>      |opRightShift       |yes      |`a >> b` |`a.opRightShift(b)`       |
|<<      |opLeftShift        |yes      |`a << b` |`a.opLeftShift(b)`        |
|--------|-------------------|---------|---------|--------------------------|
|+=      |opPlusAssign       |no       |`a += b` |`a.opPlusAssign(b)`       |
|-=      |opMinusAssign      |no       |`a -= b` |`a.opMinusAssign(b)`      |
|*=      |opTimesAssign      |no       |`a *= b` |`a.opTimesAssign(b)`      |
|/=      |opDivideAssign     |no       |`a /= b` |`a.opDivideAssign(b)`     |
|%=      |opModuloAssign     |no       |`a %= b` |`a.opModuloAssign(b)`     |
|&=      |opAndAssign        |no       |`a &= b` |`a.opAndAssign(b)`        |
|\|=     |opOrAssign         |no       |`a |= b` |`a.opOrAssign(b)`         |
|^=      |opXorAssign        |no       |`a ^= b` |`a.opXorAssign(b)`        |
|>>=     |opRightShiftAssign |no       |`a >>= b`|`a.opRightShiftAssign(b)` |
|<<=     |opLeftShiftAssign  |no       |`a <<= b`|`a.opLeftShiftAssign(b)`  |

#### Unary operators

Unary operator overloads must not take any parameters:
     
     struct foo {
         operator fun opNot() -> foo
     }
     
     val foo = foo()
     val foo2 = !foo        // is rewritten to
         foo2 = foo.opNot()
         
All unary operators must be readonly. As with binary operators, this 
does not need to be stated explicitly because that can pile up to
noise.
         
|Operator|Function Name   |readonly?|source |is rewritten to        |
|--------|----------------|---------|-------|-----------------------|
|+       |opUnaryPlus     |yes      |`-a`   |`a.opUnaryPlus()`      |
|-       |opUnaryMinus    |yes      |`-a`   |`a.opUnaryMinus()`     |
|!       |opNegate        |yes      |`!a`   |`a.opNegate()`         |
|~       |opInvert        |yes      |`~a`   |`a.opInvert()`         |
|++      |opIncrement     |yes      |`++a`  |`a.opIncrement()`      |
|--      |opDecrement     |yes      |`--a`  |`a.opDecrement()`      |


##### Postfix Increment and Decrement

Postfix increment and decrement is implemented as a different rewrite
with the `opIncrement` and `opDecrement` functions:

|source            |is rewritten to                 |
|------------------|--------------------------------|
|`++a`             |`a.opIncrement()`               |
|`--a`             |`a.opDecrement()`               |
|`a = a++`         |`a = a.opIncrement()`           |
|`b = a++`         |`b = a`<br>`a = a.opIncrement()`|
|`fn(++a)`         |`a = a.opIncrement()`<br>`fn(a)`|
|`fn(a++)`         |`fn(a)`<br>`a = a.opIncrement()`|
|`fn(a++, a++)`    |`tmp1 = a`<br>`a = a.opIncrement()`<br>`tmp2 = a`<br>`a = a.opIncrement()`<br>`fn(tmp1, tmp2)`|

         
#### Array syntax overloading

Array read and write access can be overridden, too. In fact, the
built-in array functionality uses exactly this mechanism.

The array get overload must be readonly. As with unary and binary
operators, this does not need to be stated explicitly.

|source       |function name|readonly?|is rewritten to              |
|-------------|-------------|---------|-----------------------------|
|`arr[i]`     |opGet        |   yes   |`a.opGet(i)`                 |
|`arr[i] = b` |opSet        |   no    |`a.opSet(i, b)`              |
|`arr[i] += b`|             |         |`a.opGet(i).opPlusAssign(b)` |
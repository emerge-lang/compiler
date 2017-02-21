# My Dream Language

* influenced by: Kotlin, D, Groovy, TypeScript, Java, Jai, PHP

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

### Type Modifiers

#### Type modifiers (from D)

* no modifier => mutable as usual
* readonly (called const in dlang)
* immutable
* with braces as in dlang: `alias string = immutable(Char)[]`

Those are transitive as in D; see below for variable declaration and aissgnments to variables.

Values of modified Types can be converterted to an other type according to this table. The letfomst column shows the source type, the headings show the target type.

| -           | T | readonly T | immutable T |
| ----------- | - | ---------- | ----------- |
| T           | Y | Y          | N           |
| readonly T  | N | Y          | N           |
| immutable T | N | Y          | Y           |

##### Syntax

Type modifiers can be prefixed to variable declarations to apply the
modifier to the inferred type (see below).

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
this language supports functions and methods in the sense as used in Kotlin and Java:

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

This is so that the syntax supports the matruring of a piece of code from being somewhere inlined in a function to possibly becoming a public API, as Jonathan Blow points out in one of his videos regarding his language Jai.

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
    	nestedFun = (a: Int, b: Int) -> Int {
			// some code
    	}

		c = nestedFun(a, b)
	}


	toplevelFun = (a: Int, b: Int) -> Int {
		// some code
    }


	fun toplevelFun(a: Int, b: Int) -> Int {
		// some code
    }

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

This language has classes, interfaces and structs. The syntax is more traditional like in D or Java (and less like in Kotlin). The constructor notation of TypeScript is used:

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

Struct constructors work as in D. Because this language does not know the `new` keyword, there is no syntactical difference in instatiating a class or a struct. However, as in D, the memory layout of a struct must be known at
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

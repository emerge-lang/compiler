# Compiler Architecture

This document outlines the compilers architecture and its core algorithms.

## Tokenizer

Source files are split into tokens by a Tokenizer. It discards whitespace except
for newlines.

## Parser (aka lexical analysis)

Those tokens are then parsed into an abstract syntax tree (AST). This step
is performed by the code in the `parser` module:

The file `grammar.kt` defines the grammar of the language with kotlin builders,
e.g.:

```kotlin
val ModuleDeclaration = rule {
    keyword(MODULE)

    __matched()

    identifier()

    __optimistic()

    atLeast(0) {
        operator(DOT)
        identifier()
    }
    operator(NEWLINE)
}
```

These builders put together a complex tree of `Rule`s that can be matched against
a `TransactionalSequence` of tokens. Once it is assured that a given sequence of
tokens matches a particular structure the matched tokens are "post-processed".

The sequence of matched tokens is passed on to a function that uses simple
divide-and-conquer to turn the tokens into instances of the AST classes.
See this example for a module declaration (as above):

```kotlin
private fun toAST_moduleDeclaration(tokens: TransactionalSequence<Any, Position>): ModuleDeclaration {
    val keyword = tokens.next()!! as KeywordToken

    val identifiers = ArrayList<String>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add((tokens.next()!! as IdentifierToken).value)

        // skip the dot, if there
        tokens.next()
    }

    return ModuleDeclaration(keyword.sourceLocation, identifiers.toTypedArray())
}
```

By the time the AST is fully constructed there is an AST entity per module and
top-level element:

* There is one `ASTModule` for all modules parsed
* Every `ASTModule` holds references to the AST entities of its declarations:
  * Top-Level Variables
  * Top-Level Functions
  * Data structures and their interfaces:
    * Classes with member variables and functions
    * Structs

## Putting the AST into context

Once the AST is constructed it has to be put into context. Every bit of AST needs
to know in what context it was declared. This context will be the one all semantic
analysis will be based upon.  
There will be more info on contexts later. For now it suffices to know that
`CTContext` means compile-time context.

All AST entities are converted to "Bound" entities (e.g. `ast.Variable` becomes
`binding.BoundVariable`). The differences are:

* the bound entity holds a reference to its `CTContext`
* the bound entity has accessors that can provide higher-level, type-checked
  information on the entity (e.g. a hard and reliably reference to the type
  of a variable).

## Semantic Analysis

The semantic analysis is split into multiple phases. All those phases are performed
by the bound AST entities. As much as i hate: this means that there is a set
of methods on the bound AST Rntities that have to be invoked in a particular
order (one per phase).

### Phase 1: Explicit type references

In this phase, all explicit type references on top-level declarations (variables,
functions, class members) are linked to the corresponding bound AST entity.

Every single mention of a type in the source code is wrapped into its own
instance of `TypeReference`. For every time a type is mentioned in the propgram,
there is a corresponding instance of that class.  
This phase determines the bound AST entities the loose type references point to.
This resolves imports and type aliases to a fully qualified name. The
`TypeReferences` are replaced by `BaseTypeReferences`.  
A `BaseTypeReference` not only holds the name of the type but also a reference to
the bound AST entity of the type (e.g. a class or a struct).

There is only one kind of type inference in this phase: types inferred from
literals.  So e.g. `val x = 3` will be inferred to be of type
`Int`. However, `val x = 3 + 5` will not be inferred: it involves the declaration of
`Int.opAdd` which might not be available yet.

### Phase 2: Type inference

In this phase, all implicit types are resolved. Heavy recursion is used to resolve
chains:

    fun x() = 3
    fun y() = x() + 2
    fun z() = y() - 1
    
Here, the return type of `x()` will be known from the previous phase. When `z()`
is to determine its type it will ask the `BinaryExpression` for its return type.
That expression will then ask the `InvocationExpression` for its type.

`y()` goes through the same precedure and will finally deduce
its return type from the definition of `Int.opAdd`.

The type goes back up the recursion and the `BinaryExpression` in `z()` will
deduce its return type from `Int.opSubtract`.

#### Type inference recursion

A cyclic type inference is a compile-time error:

    fun x() = y()
    fun y() = x()

Every bound AST entity has private member variables in which it keeps what
phase it currently is in and whether the method that corresponds to that phase
is currently executing. This allows the detection of recursive type inferences.
If one of these situations is encountered all types in the cyclic chain will
be `null` and no further semantic analysis is performed on their basis.

### Phase 3: Code

The semantic analysis of code requires knowledge about the elements in the
stackframe and about accessible global/top-level declarations.

Sufficient knowledge about all top-level declarations has been collected in the
previous phases; that means: the code inside functions can now be analysed.

.... do i need to go into any details on types?

.... TODO: immutable contexts and reference counting

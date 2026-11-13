# Tokens

How emerge keeps effects visible in function signatures: the rules, why they are what they are, and where the
compiler implements them.

## The idea

A function can only reach state outside of the program, or state shared across the program, through a _token_
it was passed. There are no function modifiers for effects (`pure`, `read` and `mut` functions are gone), and no
mutable global variables. The mutability of the token reference, `read` or `mut`, says whether the function
observes that state or changes it.

A token is an object that stands for state outside of itself. The type system keeps it visible: a reference
whose type says "no token" never leads to one.

```
fn greet(borrow out: mut PrintStream) {    // can write to that stream, and to nothing else
    out.println("hello")
}
```

## Tokens, non-tokens, and types that may be either

An object is a token or it is not, and its class says which: a `token class` makes tokens, every other class
does not. A type says one of three things about the objects behind it:

| the type                                                  | its values             |
|-----------------------------------------------------------|------------------------|
| a `token class` or `token interface`                      | are tokens             |
| a class not declared `token`, `NonToken` and its subtypes | are not tokens         |
| any other interface, `Any`                                | may or may not be ones |

```
token interface Clock {                           // every implementation is a token
    fn now(self) -> Instant
}
token class BufferedPrintStream : PrintStream {   // a decorator: is a token and holds one
    inner: mut PrintStream = init
}
interface Iterator<T> {                           // may be a token: an iterator over the lines of a file is one,
    fn next(self: mut _) -> T?                    // an iterator over an array is not
}
interface Shape : NonToken {                      // no implementation is a token
    fn area(self) -> F64
}
```

`Any` is the top type and takes every value, tokens included. `emerge.core.NonToken` is an interface below it.
Every class that is not declared `token` is a subtype of `NonToken` without saying so; an interface is one where
it inherits from it.

An interface describes behaviour, and whether an implementation of it reaches outside of itself is up to the
implementation. So an interface says nothing by default, and a token class implements it like any other class
does. `emerge.std.io.PrintStream` is such an interface: a stream to a file descriptor is a token, a stream that
collects text in memory is not. Code that needs a value of an interface which is no token says so:
`Iterator<S32> & NonToken`.

A type argument counts: `Box<SystemClock>` may hold a token though `Box` is no token class, so a type that
mentions a type which may be a token may be one itself. That is decided per instantiation; `Box<S32>` is no token.

## The rules

1. **A token is never frozen.** An `own` value becomes `const` only if its type cannot be a token. `const T` can
   be written for a `T` that may be a token, and its values are no tokens, as nothing else gets to be `const`. It
   is rejected for a token type, which has no `const` values.
2. **A class says what it holds.** A class with a member variable whose type may be a token must be declared
   `token`, or inherit from `NonToken` in writing. In a class that inherits from `NonToken`, such a type is
   narrowed: `pet: Animal` is `pet: Animal & NonToken`. A type parameter of the class is left as it is; the
   instantiation decides.
3. **No forgetting.** A value whose type may be a token is not assignable to a type that cannot be one, at any
   mutability. Apart from that, assignability is subtyping, and a token class is no subtype of `NonToken`.
4. **Type parameters.** A `T` may be bound to a token type, as its bound is `Any?` unless it says otherwise. So
   generic code cannot freeze a `T` or a type that mentions it, and cannot assign it to `NonToken`. `T : NonToken`
   excludes token types and allows both. This is what rules 1 and 3 say about a type with that bound; there is no
   separate mechanism. A type argument with `in` variance reads as `Any?`, which may be a token.
5. **Interfaces.** Every implementer of a `token interface` is a token class or a token interface, and has to say
   so. No token type inherits from `NonToken`.
6. **Closures.** A closure that captures a token is a token. _Not implemented:_ it comes with function types
   ([roadmap](../roadmap.md) item 13).

### What the rules guarantee

* No token is reachable from a reference of a type that cannot be a token. So `const` data never contains a
  token, and neither does a `NonToken`.
* A function with no type in its signature that may be a token cannot touch external state, whatever the
  mutability of its parameters. The exceptions are the [runtime special cases](#runtime-special-cases) and
  [the trust boundary](#the-trust-boundary).

Rule 3 is what makes this hold. Without it, a token could sit behind a field of type `NonToken` in a class that
freezes, and stay usable there: a `mut` field read through a `const` reference is `read`
(`TypeMutability.limitedTo`), and `const` widens to `read`.

Subtyping stays one transitive relation: a token class that implements `Iterator<T>` is a subtype of it, `self`
in `Iterator<T>` may be a token, and nothing needs an exception for the receiver of a call.

### What they do not guarantee

That a `read` reference to a token only observes. It holds of the tokens the platform hands out, and of a token
class as long as it holds no `Cell` (see [internal mutability](#internal-mutability)). A token class with a cell
decides what it offers through a `read` reference, and its author is trusted with that: a `read S3Bucket` sends
queries through a socket it has to write to. Nothing is forged by it, as whoever constructed the bucket had the
`mut` socket to give. There is no way to offer the distinction of `read` and `mut` to the users of a library
without trusting its author on it.

### Consequences elsewhere in the type system

**Variables.** A variable that is not `var` and has no mutability written is `const`, and an `own` value assigned
to it freezes. Where the type may be a token it is `mut` instead: `counters = Counters()` is a `mut Counters` for
a token class `Counters`.

**Combined mutabilities.** That a `const` type is no token has to survive where mutabilities are combined:
`mut A & const A` is `own A`, and so is a `const T` whose `T` is bound to `mut A`. Neither says "no token"
anymore, so the result is intersected with `NonToken`. An intersection is no token if one of its components is
none, and assigning it component by component must not lose that; so an `own` component of such an intersection
is also tried as the `const` it can become: `own Animal & NonToken` freezes into `const Animal`.

**Common supertypes.** The closest common supertype of two types that cannot be tokens is `NonToken`, not `Any`.

**Casts are not checked.** `x as NonToken` is accepted for an `x` that may be a token. The check at runtime looks
at the class of the object and does not see its type arguments, so it succeeds for a `Box<SystemClock>`, and a
token is forgotten. Casts are unsound in more ways than this one (roadmap item 12.4: `x as mut Foo` on a `read`
value is accepted as written, which defeats the mutability of token references like every other mutability).
They get no rule of their own before the runtime can check type arguments.

`t is Named` on a token is fine. Once there are smart casts, it narrows `t: SomeToken` to `SomeToken & Named`,
which is still a token type.

**Destructors** need no rule: see [class-destructors.md](class-destructors.md).

## Global variables

A top-level variable cannot be `var`, and its type must be `const`. A type argument in it may be `read`
(`Array<String>` is an array of `read String`), but not `mut` or `own`. The initializer of a global cannot obtain
a token, so it cannot have effects.

There is no replacement mechanism for mutable globals. State that the whole application shares is created in
`main` and passed down, as a parameter or captured in a field at construction:

```
token class Counters {      // `token` is optional here; it keeps the state from being frozen or forgotten
    var requests: S32 = 0
}

fn main(world: mut World) {
    counters = Counters()
    serve(StandardOut.take(world)!!, counters)
}
```

The reference to the state is its own key, and as granular as a key can be. An implementation of an interface
function receives only what the signature of that function passes; state it needs beyond that it has to capture
when it is constructed.

## Where tokens come from

Any code can construct an instance of a token class it can see the constructor of; that grants nothing, as the
object reaches only what it was given. Authority over state outside of the program comes from the root, directly
or through a `unique` class.

**The root** is `emerge.platform.World`, a token class with one instance per process. Its constructor is private
to the platform, and it has no members. It stands for the state of the process that no emerge value holds, which
includes whether each `unique` class has handed out its instance.

**`main`** takes no parameter, or the root as its only one. The author chooses the mutability:

```
fn main(world: mut World) {
    out = StandardOut.take(world)!!
    out.println("hello")
}
```

**`unique` classes** stand for a resource there is one of per process. Any code can declare one, which is how a
binding to a C library that keeps its state to itself says so:

```
export unique class LibUsb {
    private constructor {
        usb_init()
    }
    export fn devices(self: read _) -> Array<UsbDevice> { ... }
}

export fn openUsb(world: mut World) -> own LibUsb? = LibUsb.take(world)
```

* `unique` implies `token`. Only classes can be unique, and a unique class has no type parameters: there is one
  flag per class.
* The compiler adds a static function `take(world: mut World, <the parameters of the constructor>) -> own C?`.
  It constructs the instance on the first call and returns `null` on every later one. It has the visibility of
  the constructor.
* The constructor cannot be invoked in any other way, not even from inside the class.
* The flag is set when the constructor returns, so a constructor that throws leaves the instance obtainable. It
  is never reset: once the instance is destroyed, there is none for the rest of the process.
* `take` needs the root as `mut` because whether it succeeds depends on what happened in the process before, and
  because it takes the instance away from everybody else.

The platform declares its tokens this way: `emerge.platform.StandardOut` and `StandardError` are unique classes
that implement `PrintStream`. Tokens of one platform live in the package of that platform; using one a platform
does not have is a compile error.

**Factories** hand out authority that is harmless to duplicate. They are static functions on the token class
and take the root as `read`:

| token                                | obtained by                         | what takes it                                                                                              |
|--------------------------------------|-------------------------------------|------------------------------------------------------------------------------------------------------------|
| `emerge.platform.StackTraceCollector` | `StackTraceCollector.create(world)` | `collectStackTrace(collector, ...)`, `Throwable.getStackTrace(collector)`, `printTo(throwable, stream, collector)` |
| `emerge.core.AddressSpace`           | `AddressSpace.create(world)`        | `addressSpace.addressOf(value)`                                                                            |

Both are tokens because what they reveal is not a function of the program's values: where objects and code are
in memory, and who called the current function. Without the collector, a function could throw, catch, and behave
differently depending on its caller. `Throwable.setStackTrace` takes no token: it only writes into the throwable.

## Runtime special cases

Two things work without a token in the signature of the code that triggers them:

* `throw` collects the stack trace. That is no effect: the trace is written into the throwable, and reading it
  from there takes a `StackTraceCollector`.
* A panic prints the stack trace to standard error, and ends the process.

For these, the runtime holds two tokens per thread, ready before anything can throw or panic: a
`StackTraceCollector` and a stream to standard error. The backend keeps them in slots that are not emerge
globals, and passes them at the call sites the compiler generates. Emerge code cannot see the slots. The collector
owns the buffers the unwinder needs, allocated when the thread starts, so a panic can print its stack trace when
no memory is left.

`throw` invokes `emerge.core.unwind.fillStackTraceOnThrow(throwable)`, an intrinsic that is not exported. The
backend lends it the collector of the runtime: it calls `fillStackTraceUsing(throwable, collector)`, which
collects the trace and hands it to `Throwable.setStackTrace`, unless the throwable has one already.

Reference counting and allocation are not observable from emerge code and are not effects.

## The trust boundary

An `external(C)` function can do anything, and takes no token for it. Whoever declares one is responsible for
what it does, and for putting it behind a token where it has effects; a `unique` class is the tool for a library
with state of its own. `emerge.ffi.c` itself offers no way to observe an address without an `AddressSpace`.

In the standard library and the platform modules, one function is known to read state without a token: `getErrno`
in the libc module of the Linux platform.

## Effects in conditions and annotations

Two checks reason about effects without function purity:

* A condition (`if`, `while`) that uses a token as `mut`, directly or through a field, gets the "mutation in
  condition" warning. A token used as `read`, or created inside the condition, does not.
* An annotation argument must be a compile-time constant. An invocation is one if its arguments are and the
  function is not `external`.

## Internal mutability

_Not implemented_ (roadmap item 6a); what is decided:

```
token class Cell<T> {
    fn get(self: read _) -> T
    fn set(self: read _, value: T)
}
class Lazy<T : const Any?> {
    fn get(self: read _) -> T    // runs the initializer on the first call
}
```

**`Cell` is a token class,** and that is all it takes to contain it. What a cell holds is state that is not part
of the object holding the cell, shared by everyone with a reference to it; the reference is its key, like for any
other state. By rule 1 no cell is ever `const`, by rule 2 every class holding one is a token class and so never
`const` either, by rule 3 none hides behind a `NonToken`, and none is reachable from a global.

**`Lazy` is not a token class,** and not built on `Cell`: a class with a lazy member has to stay freezable and
assignable to `NonToken`. It can be, because the time of the first call does not show in the value: the value is
`const`, and the initializer captures only `const` data and no token. Rule 6 gives the second half; the first
needs function types that can say what a closure captures.

## Known gaps

* Casts can forget a token (above).
* Rule 6 is missing, as there are no closures yet.
* The flag of a unique class is a global variable of the declaring file, named `__<Class>_taken`. Code in that
  file can name and reset it until identifiers starting with `__` are rejected in user code (roadmap item 38).
* `take` is not thread-safe, and the flag is per thread in the LLVM backend, which does not matter as long as
  there is one thread (roadmap item 23).
* Anyone with a `mut` reference to a throwable can call `setStackTrace`, and so give it a trace that is not its own.
* A `StackTraceCollector` reveals where code is in memory, which overlaps with what `AddressSpace` stands for.
* The noop platform, which the frontend tests compile against, declares the platform tokens without
  implementations.

## Where it is implemented

| what                                                    | where                                                                                                         | diagnostic                                                             |
|---------------------------------------------------------|---------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------|
| `token`, `unique` on declarations                       | `parser/grammar/basetype.kt`, `ast/BaseTypeDeclaration.kt`                                                     |                                                                        |
| what a base type says (`isToken`, `isNonToken`), rule 5 | `binding/basetype/BoundBaseType.kt`, `BoundSupertypeList.kt`                                                   | `MissingTokenModifierDiagnostic`, `TokenInheritsNonTokenDiagnostic`    |
| what a type says (`mayBeToken`)                         | `BoundTypeReference` and its implementations                                                                  |                                                                        |
| rules 1, 3 and 4                                        | `TokenRule`, called from `unify` in `binding/type/RootResolvedTypeReference.kt`                                | `ValueNotAssignableDiagnostic`; `ConstTokenDiagnostic` for a written `const` |
| rule 2                                                  | `binding/basetype/BoundBaseTypeMemberVariable.kt`                                                              | `MissingTokenModifierDiagnostic`                                       |
| `NonToken` where mutabilities combine                   | `BoundIntersectionTypeReference.ofComponents` and `flippedUnify`, `GenericTypeReference.instantiateAllParameters` |                                                                        |
| variables default to `mut`; constant globals            | `binding/BoundVariable.kt`                                                                                     | `MutableGlobalVariableDiagnostic`                                      |
| unique classes: `take` and the flag                     | `ast/UniqueClassCode.kt`                                                                                       | `IllegalUniqueDeclarationDiagnostic`, `UniqueClassConstructorInvocationDiagnostic` |
| the signature of `main`                                 | `binding/BoundTopLevelFunction.kt`                                                                             | `IllegalMainSignatureDiagnostic`                                       |
| `throw` filling the stack trace                         | `binding/expression/BoundThrowExpression.kt`, `stdlib/core/unwind/collectStackTrace.em`                        |                                                                        |
| entry point, runtime slots                              | `llvm-backend`: `linux/runtime.kt`, `intrinsics/EmergeLlvmContext.kt`, `intrinsics/exception.kt`               |                                                                        |
| names the compiler relies on                            | `EmergeConstants` in `common`                                                                                  |                                                                        |

Tests are in `frontend/src/test/kotlin/compiler/negative`: `TokenErrors.kt` (the rules, one group per rule),
`UniqueClassErrors.kt` (unique classes, `main`), `GlobalStateErrors.kt` (globals), `ConditionErrors.kt`.

The rules are also part of the Rocq model of the type system, `frontend/type-system-proofs`: `is_non_token` in
`Model.v`; `may_be_token` and `unify_with_tokens` in `Subtyping.v`, a layer on `unify` that only makes assignments
fail. `OracleGrid.v` checks over the type grid (`frontend/src/test/kotlin/compiler/binding/type/grid.kt`) that
the model and the frontend agree, that nothing which may be a token is below a type that cannot be one
(`tokens_stay_visible`), and that the rules only reject (`token_rules_only_reject`). Neither is proven as a
theorem, and transitivity and the substitution lemma are not shown of `unify_with_tokens`; see #19 in
`coverage.md` there.

That the rules are enough for [what they guarantee](#what-the-rules-guarantee) is proven in `TokenGuarantee.v`
there, for a small model of a running program: classes and functions with one type parameter, a heap, and
statements that assign, read and write member variables, and construct objects. A reference whose type cannot
be a token never leads to one (`no_token_behind_a_non_token`), and code that starts without a reference that may
be a token holds no token it did not construct, constructs none that stands for state outside of the program,
and leaves every token that existed as it was (`no_token_no_effect`); both for every type the type parameter of
the code is instantiated with. The proofs use:

* the token rule on assignments, with a type argument counting and a type parameter taken for what its bound
  says (rules 1, 3 and 4);
* rule 2;
* that no token type is below `NonToken`;
* that `m T` cannot be a token where `m` is `const` or the type for `T` cannot be one, which is the `NonToken`
  that instantiation adds;
* that a member variable read through a reference is `const` only if it is declared `const`.

They do not use the rules of mutability, nor that an implementation of a token interface is a token. What the
model leaves out is listed in `coverage.md`, under "Tokens at run time".

## Left for later

* Smart casts, and with them `if (t is Named)` on a token.
* `const T` being assignable to `NonToken` for a `T` that may be a token. It is true of every such value, but
  puts the mutability into the check of the base types.
* A debug print that needs no token.
* Implicit or context parameters, should passing references through many signatures turn out to be painful. They
  shorten the call sites and leave the signatures as they are.
* Callbacks from C that need a token: another exception at the trust boundary, for the day they are needed.
* `own` values crossing threads. It would need atomic reference counts for `const` objects shared with the
  sender. Until then tokens cannot cross threads, and a worker thread has no tokens. Per-thread tokens are a
  topic for when threads are added.
* Injecting tokens into `main` by parameter type, which could be added on top of `take`.

## Decided against

* **`Any` as the type of everything that is no token, with token types outside of it.** There is no type left
  that an `if` with a token in one branch could have, and `Any` would not take any value.
* **A token class that implements an interface without being a subtype of it,** which is what a token class
  implementing a non-token interface comes to. It makes two relations of subtyping, and needs exceptions for the
  receiver of a call, for the bounds of type parameters and for casts.
* **Interfaces that cannot be tokens unless they say so.** A token class could never implement an interface
  whose author did not think of it, and no adapter helps, as it could not hold the token. The other way around,
  the user of the interface helps themselves with `& NonToken`.
* **A `token T` that has to be asked for.** It follows the interfaces: `Array<Iterator<S32>>` would be rejected.
* **A `readconst` mutability as the mechanism.** It makes a token field read through a `const` reference useless,
  but `const` is still assignable to `read`, and through a `read` reference the same field is usable again.
* **`class X : mut Any` as the notation.** It reads like ordinary subtyping while most of its meaning would be
  extra rules, and it mirrors `: const Any`, which does something else.
* **Token operations that all take `mut`.** It would need none of the rules above, but it gives up the difference
  between observing and changing external state.
* **`effect` as a keyword for an interface-like declaration.** A decorator would state its use twice, and the
  word promises effect handlers.
* **Atoms as root tokens.** An atom is reachable by name from anywhere, which is the ambient authority tokens
  remove.
* **One bundle type passed to `main`.** Platforms offer different tokens, and tokens handed out as `mut` fields
  could never be sent to another thread later.
* **`takeStandardOut(world)` and the like, one function per platform token.** Libraries need obtain-once tokens
  too, so the mechanism is a language feature, `unique`.
* **Resetting the flag of a unique class when its instance is destroyed.** Whether `take` succeeds would then
  depend on when some other code dropped its reference.
* **A global cell for application state, opened with a token as the key.** The state is reachable exactly as
  widely as the key is held. Keyed on `World`, every user of the state needs the coarsest token there is. Keyed on
  a narrower platform token, that token also grants access to unrelated state. Keyed on a type the application
  declares, the key has to be passed to every user, who could be passed the state instead. A token interface
  cannot be a key at all, as anyone can implement it.
* **Requiring every token class outside the platform to have a token field,** so that tokens can only be derived.
  A token of any type could still be wrapped into a freshly constructed, `own` object of any token interface,
  and a print stream that writes to memory could not exist without a token.
* **A token parameter on `fillStackTrace` or `Throwable.setStackTrace`.** Writing a trace into a throwable
  reveals nothing; reading it does, so reading is what takes the collector.

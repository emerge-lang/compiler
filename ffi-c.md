# FFI to C

Interaction with the OS on linux will be done by utilizing the libc on the
host system. This is a bit "unpure", but it saves a huge amount of work
and will enable Emerge to be a somewhat useful language much quicker.
To be able to utilize libc, Emerge needs a FFI for C. Additionally, it might
be desirable to utilize other C libraries to do cool projects with Emerge,
so a C FFI is a great thing to have.

Though, as the only practical use of this interface is now  to enable use of
libc, and only those parts of it that are needed to support the platform
abstractions needed for the Emerge standard library, this FFI is only extended
and fleshed out to the point where it can fulfill this purpose.  
Also, it is __not__ the goal of this FFI to allow all logic to be expressed
in Emerge that could be expressed in C. The consequence would be a
bursting-dam like abstraction leak of unsafe footguns into Emerge. Nah.

---

This file outlines how the FFI works and will detail on the design decisions
around it.

## Types

Emerge treats every value like it lives on the heap and is being referenced. Pass-by-value
is seen as an optimization done behind the compiler abstractions in Emerge. In C, this distinction
is essential. Stealing a lot from how Kotlin/Native approaches this:

* `void*` is `COpaquePointer`
* `T*` is `CPointer<T>`
* `CPointer<*> : COpaquePointer`

| C type    | Emerge type                                 |
|-----------|---------------------------------------------|
| `void`    | *n/a*, `Unit` when returned from a function |
| `void*`   | `COpaquePointer`                            |
| `size_t`  | `uword`                                     |
| `ssize_t` | `iword`                                     |
| `char`    | `Byte`                                      |
| `int`     | `Int`                                       |

## Pass-by-value vs pass-by-reference

The emerge integral types are always passed by value. To pass by reference, use `CPointer`.
Structs are passed by reference by default, so any struct `T` in Emerge maps to `T*` in C. To pass
by value, use `CValue`.

## Declaring C functions

Like in rust and D, functions using the C calling convention can be declared in Emerge and then linked
to an actual implementation from a static library or linked dynamically by the linker:

    external(C) fun getpid() -> Int

There are special types to use for arguments and return types that allow do denote C-specific concepts like
raw pointers. Using this notation you can basically write the equivalent of a C header file and invoke these
functions from Emerge code.

## Implications

Mapping C `int`, which is required to be at least 16 bits to `Emerge`s `Int`
which is required to be exactly 32 bits implies that **the C FFI cannot be
provided on platforms where Cs `int` is 16 bit.** As of 2024, with some linux
distros starting to drop support for 32-bit processors, its safe to assume that
these platforms are primarily microprocessors -> not in scope.




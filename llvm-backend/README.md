# LLVM Backend

## Memory Layout of Values

### Value Types

Even though Emerge semantically doesn't distinguish between value types and reference types,
its design still aims to allow optimization of the traditional value types (ints, floats, booleans, ...).
So, for the LLVM backend, there are value types from emerge:

| Emerge Type   | LLVM Type     |
|---------------|---------------|
| Boolean       | `i1`          |
| Byte, UByte   | `i8`          |
| Short, UShort | `i16`         |
| Int, UInt     | `i32`         |
| Long, ULong   | `i64`         |
| iword, uword  | `i<ptr size>` |

So the LLVM backend will always define based on the target architecture:
```llvm
%word = i<ptr size>
```

#### (Auto-)Boxing

Boxing is not a concept present in Emerge as a language. The LLVM backend will box value types
whenever they are assigned to one of their non-value supertypes `Number` or `Any`:

    val x: Int = 3 // value type, no heap allocation
    val y: Any = x // new heap-allocated box, gets filled with a copy of x

### Reference Types

Any value that is not of a value-type well be a heap-allocated reference type.
Emerge uses reference counting for memory management. To allow reference counting on `Any` values,
_all_ reference types (including arrays) must have the same memory layout for the reference
counter.

Hence, this is the layout that all heap-allocated values will have in common:

```llvm
%anyvalue = type {
    %word,  ; reference count
    ptr,    ; vtable pointer 
}
```

### Arrays

Arrays always live on the heap.

#### Of Reference-Types

For reference types, arrays are simple enough as they are just containers like any other type.
Hence, this is the layout for arrays of reference types:

```llvm
%refrray = type {
    %word,    ; reference count
    ptr,      ; vtable pointer
    %word,    ; element count
    [0 x ptr] ; elements, size determined at array creation
}
```

This allows
* arrays to be assigned to `Any` references
* runtime-type-checked downcasting from `Any` to `Array` (through the vtable pointer)

#### Of Value-Types

When the element type of the array is known to be a value type, the `ptr` to the array can be simplified to this:

```llvm
%valuearray = type {
    %word,           ; reference count
    %word,           ; element count
    [0 x %valuetype] ; elements, size determined at array creation
}
```
#### (Auto-)Boxing

`Array<Int>` could just always be an array of boxed `Int`s. But that's bad for performance when dealing
with lots of binary-ish data. So the compiler must be able to optimize an `Array<Int>` or `Array<Byte>`
to a contiguous block of memory.

Though, doing that poses another boxing problem:

```
val x: Array<Int> = [1, 2, 3, 4]
val y: Array<out Any> = x
```

This is legal in Emerge. Though, it would require copying the array and boxing every value :(
While that's at least functionally correct for immutable content, it stops working with `mutable Array<Int>`
because changes in `x` will then not propagate to `y`.

The solution:

* `Array<in T>` for any `T` is always a boxed version
* `Array<T>` and `Array<out T>` where `T : Value`
  * is always a value-array. The element size is known, no need for
    a vtable pointer
  * the backend can safely emit direct access into the elements as the element-size is known at compile-time
* `Array<T>` where `T : Reference`
  * if there is a `T2 != T` where `T2 : Value, T` then the `Array<T>` is an array-box (see layout below).
    direct access into the elements is forbidden; the backend must emit dynamic-dispatch for accessing the elements
    so the array-box can handle the boxing logic
  * if there is **no** `T2 != T` where `T2 : Value, T`, then `Array<T>` is a reference-array. The direct elements
    are known to be `ptr`s to the actual elements on the heap, and direct access into the elements without the `vtable`
    is possible.

##### The Array-Box

Has this layout in memory:

```llvm
%arraybox = type {
    %word,  ; reference count
    ptr,    ; vtable pointer, set according to the type of the underlying value-array
    ptr,    ; pointer to the value-array that is being boxed
}
```

This allows the array-box to conform to the `Any` type, and through dynamic dispatch to normalize the elements
of unknown size. E.g. consider the Array-Box for `Byte`: the vtable would define these methods (pseudo-code):

```
fun size(self: readonly ArrayBox) -> uword {
    val byteArray = self.llvmStructEntry_valueArrayPtr as Array<Byte>
    return byteArray.llvmStructEntry_size
}
fun get(self: readonly ArrayBox, index: uword) -> Number {
    val byteArray = self.llvmStructEntry_valueArrayPtr as Array<Byte>
    val rawByte = byteArray.get(index)
    return ByteBox(rawByte)
}
fun set(self: mutable ArrayBox, index: uword, valueBox: ByteBox) {
    val byteArray = self.llvmStructEntry_valueArrayPtr as Array<Byte>
    byteArray.set(index, valueBox.value)
}
```

## Reference Counting

* every heap-allocated object has a reference count (see layout above)
* when a reference-value is assigned to a local variable, struct member object member, the reference count must be
  incremented by 1
    * `val x: Any = Unit` increments the ref-count for `Unit`
* when passing a reference-value to a function (or a dynamic setter of an object member), the reference count
  must be increased **by the callee**. This avoids unnecessary counting on parameters that are ignored by the callee.
* when a local variable or function parameter goes out of scope (regardless the reason), the reference count must be
  decremented by 1
  * obvious exception are unused function parameters. not incremented, so not decremented
* returning a value from a function counts as creating a new reference to it, so its reference count must be
  incremented. A function returning the only reference ot a value will pass it back to the caller with a
  reference count of `1`.
* after calling a function
  * when the return value is not used, the reference count must be decremented by 1
  * when the return value is used, its reference count must not be incremented.
* when an object is dropped all the reference-counter of all the objects references from member variables must
  be decremented.
* whenever the reference count of a value is decremented, the acting code must subsequently check whether the reference
  count is 0. If that's the case the code that just dropped the reference(count) needs to invoke the drop function
  for the reference (see below).

### The drop function

The `platform` package of each target must provide two drop functions. One for value-arrays, another for reference values,
which includes reference-arrays and array-boxes.
This function would also call the open `finalize` method on the reference objects, serving two purposes:
* handle nested references decrementing and dropping
* closing external resources like sockets, file handles, ...

Here is an example implementation using libc:

```
// void free (void *ptr) from libc
external(C) fun free(ptr: COpaquePointer) -> Unit

fun __dropReference(object: Any) {
    val pointer = object as CPointer<uword>
    
    // the counter is always at the start of the object
    assert(pointer.pointed == 0) { "Reference count not 0 when dropping: premature deallocation" }
    
    object.finalize()
    free(pointer)
}

fun __dropValueArray(arrayPointer: CPointer<uword>) {
    assert(pointer.pointed == 0) { "Reference count not 0 when dropping: premature deallocation" }
    
    free(pointer)
}
```

### Singletons (like the unit value)

Singletons declared using the `object` keyword must never be deallocated. This is achieved by simply starting their
lifetime with a reference count of `1`, so it will never drop to 0.
This conveniently allows the `Unit` type+object to be declared completely in Emerge with very little code:

    immutable object Unit {}

## Dynamic Dispatch (vtable)

Downcasting from one class to a subclass is generally a sign of bad code design. However, downcasting to an 
interface type is a tool that can be very useful in adapting one piece of code to the abilities and properties
of some other code, dynamically at runtime.

Union and intersection types are a very useful concept when trying to get the static typing out of the
programmers way: `A | B` and `A & B`.

Combining these two, we can denote that a single value has multiple capabilities:

    interface S
    interface A

    fun doSomething(obj: S & A) {
    }


Having a separate vtable for each abstract type makes downcasting very complicated and union+intersection types
even more complicated (if not impossible) to implement. Hence, the vtable design for Emerge is more sophisticated
to enable these features.

----

The emerge vtables are essentially a hash map designed for quick access, to minimize the performance penalty on
dynamic dispatch

### How vtables are built

There is a vtable for each _concrete_ type; as for the concrete type all the abstract supertypes are known and can
be considered. Each method signature/overload gets a hash-value assigned to it. The hash is of the same size as the
targets word-size. Knowing all the hashes of a concrete type, the backend will find the shortest prefix of all of the
hashes that still keeps them unique. So e.g. these hashes:

| Hash                 | Function          |
|----------------------|-------------------|
| `0x9DEE000007F32200` | `finalize()`      |
| `0x4ECAD20890000000` | `foo(x: Int)`     | 
| `0x522773FF24CB1A07` | `foo(x: Boolean)` |

Then there can be these prefixes:

| Prefix   | Function                 |
|----------|--------------------------|
| `0b1001` | `finalize()`             |
| `0b0100` | `foo(x: Int)`            | 
| `0b0101` | `foo(x: Boolean) -> Int` |

The unique prefix length is 5 bits. So the function entires for our vtable will be 2<sup>5</sup> entries/words big.
At the location of each functions prefix there would be the address of that functions code.

    Offset/Prefix   Value                Function
    0b00000         0x0000000000000000
    0b00001         0x0000000000000000
    0b00010         0x0000000000000000
    0b00011         0x0000000000000000
    0b00100         0x0000000000056de0   foo(x: Int)
    0b00101         0x00000000000a183c   foo(x: Boolean)
    0b00110         0x0000000000000000
    0b00111         0x0000000000000000
    0b01000         0x0000000000000000
    0b01001         0x0000000000000000
    0b01010         0x0000000000000000
    0b01011         0x0000000000000000
    0b01100         0x0000000000000000
    0b01101         0x0000000000000000
    0b01110         0x0000000000000000
    0b01111         0x0000000000000000
    0b10000         0x0000000000000000
    0b10001         0x000000000006c551   finalize()
    0b10010         0x0000000000000000
    0b10011         0x0000000000000000
    0b10100         0x0000000000000000
    0b10101         0x0000000000000000
    0b10110         0x0000000000000000
    0b10111         0x0000000000000000
    0b11000         0x0000000000000000
    0b11001         0x0000000000000000
    0b11010         0x0000000000000000
    0b11011         0x0000000000000000
    0b11100         0x0000000000000000
    0b11101         0x0000000000000000
    0b11110         0x0000000000000000
    0b11111         0x0000000000000000

The remaining entries can be filled with the address of a function that just panics the process informing
about a misled dynamic dispatch.

To go from a statically available function hash to its location in the vtable, we need to truncate the
hash to the unique prefix. This is easily done using a `lshr` instruction. So, for vtable above we'd need
to shift the hash right by (64 - 5) = 59 bits to obtain the prefix in the lower 5 bits. This `59` value
is stored in the vtable, too, for quick access during a dynamic dispatch.

The vtable needs some more information to be useful:

```llvm
%vtable = type {
    ptr,       ; pointer to the reflection data about the concrete type
    %word,     ; lshr offset for the function hashes
    [0 x ptr]  ; the vtable blob, as stated above 
}
```

### How vtables are accessed for a dynamic dispatch

`obj`/`%obj` is the variable holding the `ptr` to the object we're dispatching on, and we're calling
the `foo(Boolean) -> Int` method on that object.

in Emerge:
```
obj.foo(false)
```

gets compiled to:
```llvm
%vtablePtr = getelementptr %anyvalue, ptr %obj, i32 0, i32 1
%shiftAmountPtr = getelementptr %vtable, ptr %vtablePtr, i32 0, i32 1
%shiftAmount = load i64, ptr %shiftAmountPtr, align 8
%shortHash = lshr i64 u0x522773FF24CB1A07, %shiftAmount
%offsetIntoVtable = getelementptr %vtable, ptr %vtablePtr, i32 0, i32 2, i64 %shortHash
%targetAddress = load ptr, ptr %offsetIntoVtable, align 8
%returnValue = call i32 %targetAddress(i1 false) 
```

## Considerations re. memory layout

Placing the reference counter first was supposed to make reference counting faster. Dynamic dispatch
is quite complex in LLVM already, and gets even more complex in actual assembly. Putting the vtable pointer
first to avoid the pointer arithmetic on dynamic dispatch doesn't simplify the assembly significantly on
any of the architectures i tried it on. So the effect of that seems to be very small (judging just by
reading assembly in compiler explorer). Maybe we can revisit this once the compiler is mature enough to run
a benchmark on this.
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

The LLVM backend will always define based on the target architecture:
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
    ptr,    ; typeinfo pointer
    ptr,    ; weak reference collection pointer (see below) 
}
```

### Arrays

Arrays always live on the heap.

#### Of Reference-Types

For reference types, arrays are simple enough as they are just containers like any other type.
Hence, this is the layout for arrays of reference types:

```llvm
%refarray = type {
    %anyvalue ; base for all objects
    %word,    ; element count
    [0 x ptr] ; elements, size determined at array creation
}
```

This allows
* arrays to be assigned to `Any` references
* runtime-type-checked downcasting from `Any` to `Array` (through the typeinfo pointer)

#### Of Value-Types

When the element type of the array is known to be a value type, layout of the array on heap
can be simplified to this:

```llvm
%valuearray = type {
    %word,           ; reference count
    ptr,             ; weak reference collection pointer
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
    a vtable
  * the backend can safely emit direct access into the elements as the element-size is known at compile-time
* `Array<T>` where `T : Reference`
  * if there is a `T2 != T` where `T2 : Value, T` then the `Array<T>` is an array-box (see layout below).
    direct access into the elements is forbidden; the backend must emit dynamic-dispatch for accessing the elements
    so the array-box can handle the boxing logic
  * if there is **no** `T2 != T` where `T2 : Value, T`, then `Array<T>` is a reference-array. The direct elements
    are known to be `ptr`s to the actual elements on the heap, and direct access into the elements without the vtable
    is possible.

##### The Array-Box

Has this layout in memory:

```llvm
%arraybox = type {
    %anyvalue ; base for all objects, vtable set according to the type of the underlying value-array
    ptr,      ; pointer to the value-array that is being boxed
}
```

This allows the array-box to conform to the `Any` type, and through dynamic dispatch to normalize the elements
of unknown size. E.g. consider the Array-Box for `Byte`: the vtable would define these methods (ignoring ref counting for clarity):

```llvm
%valuearray_byte = {
    %word,
    ptr,
    %word,
    [0 x i8]
}
%bytebox = {
    %anyvalue,
    i8
}

define %word @arrayBoxByte_size(ptr %self) {
    %rawArrayPtr = getelementptr %arraybox, ptr %self, i32 0, i32 1
    %sizePtr = getelementptr %valuearray_byte, ptr %rawArrayPtr, i32 0, i32 2
    %size = load %word, ptr %sizePtr
    ret %size
}
define ptr @arrayBoxByte_get(ptr %self, %word %index) {
    %rawArrayPtr = getelementptr %arraybox, ptr %self, i32 0, i32 1
    %rawBytePtr = getelementptr %valuearray_byte, ptr %rawArrayPtr, i32 0, i32 3, %word %index
    %rawByte = load i8, ptr %rawBytePtr
    %boxPtr = call ptr @ByteBoxCtor(i8 %rawByte)
    ret %boxPtr
}
define void @arrayBoxByte_set(ptr %self, %word %index, ptr %valueBox) {
    %rawByteSourcePtr = getelementptr %bytebox, ptr %valueBox, i32 0, i32 1
    %rawByteSource = load i8, ptr %rawByteSourcePtr, align 1
    %rawArrayPtr = getelementptr %arraybox, ptr %self, i32 0, i32 3
    %rawByteTargetPtr = getelementptr %valuearray_byte, ptr %rawArrayPtr, i32 0, i32 3, %word %index
    store i8 %rawByteSource, ptr %rawByteTargetPtr, align 1
    ret void
}
declare ptr @ByteBoxCtor(i8 %value)
```

## Reference Counting

* every heap-allocated object has a reference count (see layout above)
* when a reference-value is assigned to a local variable, struct member or object member, the reference count must be
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
    
    nullWeakReferences(object)
    
    object.finalize()
    free(pointer)
}

fun __dropValueArray(arrayPointer: CPointer<uword>) {
    assert(pointer.pointed == 0) { "Reference count not 0 when dropping: premature deallocation" }
    
    nullWeakReferences(object)
    
    free(pointer)
}
```

_`nullWeakReferences` is described further below._

### Singletons (like the unit value)

Singletons declared using the `object` keyword must never be deallocated. This is achieved by simply starting their
lifetime with a reference count of `1`, so it will never drop to 0.
This conveniently allows the `Unit` type+object to be declared completely in Emerge with very little code:

    immutable object Unit {}

### Weak references

Weak references are denoted by the regular type `Weak<T>` that gets amended with special treatment by the
llvm backend:

    struct Weak<T : Any> {
        value: T?
    }

The special treatment is:
* creating a new `Weak<T>(t)` does _not_ increase the reference counter of `t`
* instead, the compiler registers this instance of `Weak` in the weak reference collection of `t`.
* the `Weak<T>` is itself strongly reference counted
* when a `Weak` is dropped and the referred value is still present, it removes itself from the
  weak reference collection of its value.

This mechanism is described here.

#### The weak reference collection

The `%anyvalue` type described above that is a prelude to _all_ reference counted objects on the heap
contains a `ptr` to what is called the "weak reference collection". If there are 0 weak references to that
object, this `ptr` must be `null`. When there are, it points to a special linked list of arrays, holding pointers
to the `Weak`s referencing the object:

```llvm
%weakReferenceCollection = type {
    [10 x ptr],  ; space for up to 10 weak references
    ptr          ; nullable pointer to a further %weakReferenceCollection (linked list)
}
```

_The linking in this structure gives the ability to have an arbitrary amount of weak references to each
object. The array-ing aims to amortize the cost of the linking to some extent._

#### Creating a new weak reference

1. allocate a `Weak` on the heap. This initializes the `value` to `null`.
2. if the weak-reference-collection pointer of the target object is `null`:
   1. allocate a new `%weakReferenceCollection` on the heap
   2. write the pointer to the newly created `Weak` into the first element of the `[10 x ptr]` array
3. else:
   1. walk the linked list of `%weakReferenceCollection` values, on each
   2. iterate the `[10 x ptr]` array
   3. if one `null` ptr is found, write the pointer to the newly created `Weak` into that location
   4. else:
      1. allocate a new `%weakReferenceCollection` on the heap
      2. write the pointer to the newly created `Weak` into the first element of the `[10 x ptr]` array
      3. link the newly created `%weakReferenceCollection` to the last one already linked from the target object

#### Dropping a weak reference

1. abort if the `value` is already `null`
2. walk the linked list of `%weakReferenceCollection` values, on each
3. iterate the `[10 x ptr]` array, on each
4. if this is the ptr to the `Weak` that is being dropped:
   1. set it to `null`
   2. if now the whole `[10 x ptr]` array is `null`s:
   3. remove that `%weakReferenceCollection` from the linked list
   4. if this was the only `%weakReferenceCollection` in the linked list
      1. set the weak-reference-collection pointer of the target object to `null`
   5. deallocate the removed `%weakReferenceCollection`

#### Nulling weak references

When the last strong reference to an object is to be dropped, all the weak references have to be
null-ed before the object is actually touched for finalization. To achieve this, there are backwards
references from the object to all `Weak`s pointing to it, so this is trivially possible.

1. walk the linked list of `%weakReferenceCollection` values, on each
2. iterate the `[10 x ptr]` array, on each
   1. interpret that `ptr` as a reference to a `Weak`, which it is
   2. set the `value` entry to `null`, ignoring any mutability typing
3. deallocate the `%weakReferenceCollection` that was just nulled

The last point here has an implication, though: `Weak`s can always be mutated by the runtime, caused
by potentially totally external events that drop the last strong reference to the `T`. Consequently,
the compiler frontend must implement a special rule: `Weak`s can _never_ be `immutable`.

#### Goals (why all this effort??, design reasoning)

Highly recommended read: https://verdagon.dev/blog/surprising-weak-refs

The goals i had for my reference counting were:
* when a value gets dropped, _it gets dropped!_. No zombies. The overhead, no matter how much, happens at predictable
  reproducible places/times.
  * the problem with swifts approach: if you keep the allocation around until all weak references had a chance to see
    that the object is gone, the allocation can stick around for a _long_ time. Especially because the entire **point**
    of weak references is to use them seldomly. This approach creates sort of a memory leak. Yuck!
* a global list/table of weak references like Objective-C has it always seemed ugly to me. This article confirms it,
  so this is by definition not an option.
* if a large amount of objects get dropped, it should be possible to hand memory back to the OS. The JVM not doing that
  is an infamous ops problem when running lots of JVMs.
* the generational references used by vale are a _beautiful_ solution. Very lean and efficient. However, they also require
  keeping the allocation around _forever_.
  * Yes, reuse is possible, and probably prevents much memory from leaking. **But** it is impossible to return heap
    memory back to the OS, as you always need that tombstone around so your weak references don't break. I dislike this
    a lot, too. It becomes impossible to have your application consume lots of memory at startup, and then hand a large
    portion of that back to the OS for long-term low-memory operation.

But, there is one property of Emerge that comes to the rescue. I didn't plan for this, i didn't see it coming.
But it is a godsent for weak references! That property is: _memory is not shared across threads_. Objective-C needs
a _global_ mutex on its Weak-Reference-Map to deal with multithreading. Swift can use atomic increment/decrement
on the weak reference counter to deal with multithreading. Emerge doesn't need that. Whatever reference counting
mechanism i choose for Emerge, it will only ever be used by one thread _across time_ (not just at any given time).
Hence, Emerge gets away with this slightly wonky linked-list-of-arrays structure.

## Dynamic Dispatch (vtable)

Downcasting from one class to a subclass is generally a sign of bad code design. However, downcasting to an 
interface type is a tool that can be very useful in adapting one piece of code to the abilities and properties
of some other code, dynamically at runtime.

Union and intersection types are a very useful concept when trying to get the static typing out of the
programmers way: `A | B` and `A & B`. It allows to denote that a single value has multiple capabilities:

    interface S
    interface A
    interface B

    fun doSomething(obj: S & (A | B)) {
    }

I conjecture that combining the concept of downcast-to-interface-type and combinatory types yields enough
benefit in terms of freedom to write code that it's worthwhile to invent another dynamic-dispatch algorithm
than the one used in C-like languages traditionally.

Having a separate vtable for each abstract type makes downcasting very complicated and union+intersection types
even more complicated (if not impossible) to implement. Hence, the vtable design for Emerge is more sophisticated
to enable these features.

----

The emerge vtables are essentially a hash map designed for quick access, to minimize the performance penalty on
dynamic dispatch.

### How vtables are built

There is a vtable for each _concrete_ type; as for the concrete type all the abstract supertypes are known and can
be considered. Each method signature/overload gets a hash-value assigned to it. The hash is of the same size as the
targets word-size. Knowing all the hashes of a concrete type, the backend will find the shortest prefix of all the
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

Last but not least, there needs to be a mechanism to determine a values supertypes at runtime to typecheck
downcasts. The vtable of a type is defined to be the type metadata for that type. So, each vtable stores a list
of its supertypes. `Any` is never mentioned explicitly in that list.
To avoid having to search a tree for an `instanceof`, every typeinfo should contain _all_ supertypes of the
type being describe, transitively.

```llvm
%typeinfo = type {
    %word,     ; lshr offset for the function hashes
    ptr,       ; pointer to a %valuearray of ptrs, each pointing at the vtable of one of the supertypes
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
define ptr @getDynamicCallAddress(ptr %anyvalue_reference, %word %hash) {
    %typeinfoPtr = getelementptr %anyvalue, ptr %anyvalue_reference, i32 0, i32 1
    %shiftAmountPtr = getelementptr %typeinfo, ptr %typeinfoPtr, i32 0, i32 0
    %shiftAmount = load %word, ptr %shiftAmountPtr, align 8
    %shortHash = lshr %word %hash, %shiftAmount
    %offsetIntoVtable = getelementptr %typeinfo, ptr %typeinfoPtr, i32 0, i32 2, i64 %shortHash
    %targetAddress = load ptr, ptr %offsetIntoVtable, align 8
    ret %targetAddress
}

; this is the actual call
%targetAddress = @getDynamicCallAddress(ptr %obj, %word u0x522773FF24CB1A07)
%returnValue = call i32 %targetAddress(i1 false)
```

### instanceof checks

For a literal `instanceof` function in the language and for runtime-checking `as` casts, there needs to be
an underlying function that analyzes the vtable to find this out. Its a linear search along the list of supertypes,
so:

```llvm
@AnyTypeinfo = global %typeinfo
define ptr @getAnyTypeinfoPtr() {
  ret ptr @AnyTypeinfo
}
define ptr @getSupertypePtrArray(ptr %anyvalue_ref) {
  %typeinfoPtrPtr = getelementptr %anyvalue, ptr %anyvalue_reference, i32 0, i32 1
  %typeinfoPtr = load ptr, ptr %typeinfoPtrPtr
  %arrayPtr = getelementptr %typeinfo, ptr %typeinfoPtr, i32 0, i32 1
  ; elided: increase refcount for %arrayPtr
  ret ptr %arrayPtr
}
define ptr @getTypeinfoPtrOfType(ptr %typePtr) {
  ret %typePtr
}
```

```
intrinsic fun getAnyTypeinfoPtr() -> COpaquePointer
intrinsic fun getSupertypePtrArray(ref: Any) -> Array<COpaquePointer>
intrinsic fun <reified T : Any> getTypeinfoPtrOfType() -> COpaquePointer

fun <reified T : Any> isInstanceOf(self: Any) -> Boolean {
    val typePointerToCheck = getTypeinfoPtrOfType::<T>()
    if (typePointerToCheck == getAnyTypeinfoPtr()) {
        return true
    }
    val supertypes: Array<COpaquePointer> = getSupertypePtrArray(self)
    return supertypes.contains(getTypeinfoPtrOfType::<T>()) 
}

// this can then be used as such:
val x: Any = "foobar"
val isString = x.isInstanceOf::<String>()
val asString = x as String // typechecked cast
val asNumber = x as? Number // typechecked cast

assert(isString == true)
assert(asString == x)
assert(asNumber == null)
```

## Considerations re. memory layout

Placing the reference counter first was supposed to make reference counting faster. Dynamic dispatch
is quite complex in LLVM already, and gets even more complex in actual assembly. Putting the vtable pointer
first to avoid the pointer arithmetic on dynamic dispatch doesn't simplify the assembly significantly on
any of the architectures I tried it on. So the effect of that seems to be very small (judging just by
reading assembly in compiler explorer). Maybe we can revisit this once the compiler is mature enough to run
a benchmark on this.
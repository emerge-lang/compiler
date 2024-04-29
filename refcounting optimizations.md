# Optimizations to Reference Counting

See the general rules for refernce counting in [README.md]()

The foundation of the optimizations are three things:

1. The fact that no heap object can be shared between threads, so data races need not be considered
2. This rule for reference counting:
   > Returning a reference from a function call counts as creating a reference. On return, the refcounter
   > must reflect the reference the returning function has on its stack. The caller must decrement the refcounter
   > immediately when discarding the value, or possibly later when the reference goes out of scope.
3. This rule for reference counting:
   > The callee-function is responsible for incrementing the refcounter of parameters

Importantly, constructors count as functions. Newly created heap objects always start their life with a refcount
of `1`.

## References on the stack

Newly created objects will always have their first reference on the stack of the code that called the constructors.
Incrementing the refcount after a constructor invocation would be incorrect and can be avoided.

### When no reference to an object is stored in the heap during the objects lifetime

Suppose an object is only used in the stackframe of the function that created it, e.g.:

    struct Foo {
        x: S32
    }
    fun main() -> S32 {
        val foo = Foo(3)
        return foo.x
    }

This requires no _increment_ operation of `foo`s refcounter. Further, if the compiler can proof that the
`foo` reference is nevery copied to a location on the heap, the compiler can omit the _decrement_ operation
on `foo`s refcounter and instead call the destructor directly at the end of the function.

### Parameters that are only borrowed

When a function only borrows a parameter (does not create references on the heap to the parameter itself), this logic
applies:

1. function enters, refcount increases by 1
2. function runs, but only has reference to the parameter on its own stack
3. function completes, refcount decreases by 1

As the function itself does not create heap references to the parameter, the refcount cannot be observed by
any other code outside the stackframe. Hence, the compiler can skip the refcounting in this case.

This even applies when the parameter is passed to another function where its not known whether it creates heap-references
to the object. Consider this code:

    struct Foo {
        x: S32
    }

    fun a(p: Foo) {
        // does not create a heap reference to p
    }
    var global: Foo? = null
    fun b(p: Foo) {
        global = p // <-- creates a heap reference to p
    }
    fun c(p: Foo) {
        if randomBoolean() {
            a(p)
        } else {
            b(p)
        }
    }

    fun main() -> S32 {
        val foo = Foo(3)
        c(foo)
        return foo.x
    }

Note that `a` does not need to touch the refcounter of `p` at all, and that `b` needs to increment it because
it stores a reference on the heap.
Now, looking at `c`: it does not create a heap reference to `p` itself. When it chooses to call `a` it is trivially
correct for `c` to not touch the refcounter either. It is also correct for `c` to not touch the refcounter for `p`
when it calls `b`, though: `b` has the responsibility for the references it creates, and if only `b` increments the
counter, the counter will correctly be `2` when `c` returns to `main`.

In this case, `main` need not do any increment the refcounter for `foo` itself because it doesn't create any heap
references to it. But because the reference has been passed to another function, `main` may not simply destruct `foo`
on completion. It has to properly drop the reference by decrementing the refcounter and invoking `foo`s destructor
iff the counter is `0`.

### Return values

Stack-local variables that, at any point in the function body get assigned the return value of a function call,
need to be properly refcounted. After all, the function could have returned a reference obtained from the heap.
On assignment, no ref counting is needed because the increment-on-return rule accounts for it. Though, when that
variable goes out of scope, a proper drop of the variable needs to be performed (decrement plus deallocate iff
counter is `0`).

### Returning a parameter

This scenario might seem a bit tricky:

    fun a(p1: Foo, p2: Foo) {
        if randomBoolean() {
            return p1
        } else {
            return p2
        }
    }

However, given all of the above, it works out just fine:

The compiler can proof for both `p1` and `p2` that `a` creates no references on the heap and doesn't
pass them to other functions. So if it weren't for the `return` statements, `a` doesn't need to do any ref counting.

But there are returns. And these can be handled 100% regularly as any other return according to the refcounting rules;
the count must be incremented by 1.

So, consider a caller of `a`:

    fun b() -> S32 {
        val foo1 = Foo(2)
        val foo2 = Foo(3)
        val selected = a(foo1, foo2)
        return selected.x
    }

Let's look at the reference counters on each line and assume `a` selects `p1`:

| line                 | refcount `foo1` | refcount `foo2` | comment                                                                                                                                |
|----------------------|-----------------|-----------------|----------------------------------------------------------------------------------------------------------------------------------------|
| `val foo1 = Foo(2)`  | 1               |                 |                                                                                                                                        |
| `val foo2 = Foo(3)`  | 1               | 1               |                                                                                                                                        |
| `a(foo1, foo2)`      |                 |                 | `a` doesn't increment refcounters for parameters                                                                                       |
| `return p1`          | + 1 = 2         | 1               | `a` increments `p1` because its returned                                                                                               |
| `val selected = ...` | 2               | 1               | no increment because assignment to a stack variable                                                                                    |
| `return selected.x`  | 2               | 1               | increment refcount for x (nop because its a value type)                                                                                |
| end of `b`           | -1 = 1          | - 1 = 0         | `foo1` and `foo2` go out of scope. Because the references have been "leaked" to `a` a proper drop is performed. `foo2` gets finalized. |
| end of `b`           | -1 = 0          |                 | `selected` goes out of scope. Because it got in touch with the outside world (`a`), a proper drop is performed. `foo1` gets finalized. |


## Temporary Values, semi-SSA output of the frontend

When expressions are nested into each other, e.g. `foo(bar(), 3 + 4 + x)`, temporary values need to be created.
As far as reference counting is concerned, these should be treated exactly as if they were stack-local variables.
This becomes apparent if we write that expression in semi-SSA form:

    val temp1 = bar()
    val temp2 = 3 + 4
    val temp3 = temp2 + x
    val tempResult = foo(temp1, temp3)

Backends can do this transformation comparatively simply, but it's still work. Also, when then doing non-optimized
reference counting on this code, the resulting machine code is littered with reference counting all over, arguably
consisting of >80% just reference counting code.  
That reference counting code can be optimized to the absolutely needed minimum. LLVM won't do it, the emerge
compiler has to do it. And as it requires complex analysis of how state mutates in the program, the emerge backends
are a bit late to the party to be able to pull this of nicely. So, I conclude:

* the frontend should implement
  * all the logic to figure out when reference counting is needed
  * including optimizations to reduce that noise
* the IR communicated to emerge backends should _unambiguously_ contain that information, e.g. nodes such as
  `IrRefcountIncrementStatement`, `IrRefcountDecrementStatement`. Also, get rid of IR data types that can
  hold arbitrarily nested expressions and rather introduce non-re-assignable temporaries, e.g.
  `IrTemporaryCreateStatement` and `IrTemporaryValue`. So e.g. an `IrAssignmentStatement` would
  no longer reference an arbitrarily nested `IrExpression`, but rather a simple `IrTemporaryValue`.
  * **!! Attention** reference counting information should also be emitted for integral/primitive types. Treating
    these as non-heap-allocated data is a pure backend optimization, the frontend musn't care!
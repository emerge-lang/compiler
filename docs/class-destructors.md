# Class Constructors and Destructors

random notes i want to persist for future inclusion in proper language documentation

## Destructors

Destructors don't take a side effect classifier (like `pure` or `readonly`). They can always have side
effects. Side effects are their only purpose: closing externally managed resources (e.g. GPU memory, a file
handle, a window in a window manager) that would be otherwise impractical to manage through the program stack.

It is still preferred to use try-with-resources style stack controlled resource management wherever practical,
like Javas `AutoCloseable`.

But doesn't that lead the entire pure/readonly/mutating classification of other code ad-absurdum?
Yes, one would think so. Destructors could run any time, and are as such out of the control of
code that is classified as pure or readonly. So, any pure or readonly function can have side effects
injected into it through a destructor.  
**That is wrong!** Destructors cannot run _just whenever_. They run when a reference that is stored on the
heap gets changed or removed. Doing so requires mutable access to things. `pure` and `readonly` functions cannot
do that to any global variables. So no danger from that angle. For parameters its more tricky. But again,
to trigger a reference count decrease and thus a potential destructor call, the code needs to change data on 
the heap. And that requires a `mutable` reference. This means that a straightforward pure or readonly function
does not run the danger of having hidden side-effects. This can only happen when it takes `mutable` parameters.
And that seems fine to me as of writing this. E.g.:

```
class SideEffectOnEndOfLife {
    destructor {
        println("Side effect!")
    }
}

pure fun a(p: Array<SideEffectOnEndOfLife>) {
    // cannot have side effects. Even if references are created to elements in the array
    // and then removed again, it cannot possibly drop the refcounter to 0. No destructor
    // will ever be invoked here
}

pure fun b(p: mutable Array<SideEffectOnEndOfLife>) {
    set a[0] = SideEffectOnEndOfLife()
    // this is a different story now. The function can change the contents of the parameter
    // and if there are no other references than that in the array, the assignment will trigger
    // the destructor and the side effect
    
    // i think this is acceptable, as the side effect must be explicitly and actively marked
    // by the programmer in the public-facing API signature
}
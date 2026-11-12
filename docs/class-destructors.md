# Class Constructors and Destructors

random notes i want to persist for future inclusion in proper language documentation

## Destructors

Destructors have side effects as their only purpose: closing externally managed resources (e.g. GPU memory, a
file handle, a window in a window manager) that would be otherwise impractical to manage through the program
stack.

It is still preferred to use try-with-resources style stack controlled resource management wherever practical,
like Javas `AutoCloseable`.

But doesn't that lead the reasoning about effects by tokens ad-absurdum? A function without a token in its
signature is supposed to have no effect on the outside, and a destructor could run inside of it.  
**It doesn't.** A destructor takes no parameter but `self`. So it reaches the outside only through what the
object holds, and an object that holds a token is a token itself (or calls an `external(C)` function, which is
the trust boundary anyhow). A value that is no token has a destructor without effects, wherever it runs.

And a token cannot get into a function unseen: it cannot be forgotten in a type that is no token. So the
destructor of a token can only run in a function whose signature shows that token, or something that holds it.
Even then, destructors cannot run _just whenever_: they run when the last reference goes away, which takes
an `own` value handed to the function, or `mut` access to the place the reference is stored in. E.g.:

```
token class SideEffectOnEndOfLife {
    out: mut PrintStream = init
    destructor {
        self.out.println("Side effect!")
    }
}

fn a(borrow p: read Array<SideEffectOnEndOfLife>) {
    // cannot have side effects. Even if references are created to elements in the array
    // and then removed again, it cannot possibly drop the refcounter to 0. No destructor
    // will ever be invoked here
}

fn b(borrow p: mut Array<SideEffectOnEndOfLife>, replacement: SideEffectOnEndOfLife) {
    set p[0] = replacement
    // this is a different story now. The function can change the contents of the parameter
    // and if there are no other references than that in the array, the assignment will trigger
    // the destructor and the side effect

    // this is acceptable, as the side effect is explicitly and actively marked
    // by the programmer in the public-facing API signature: a mut parameter that holds tokens
}
```

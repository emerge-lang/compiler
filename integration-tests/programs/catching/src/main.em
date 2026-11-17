package catching

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

class Oops : Throwable {
    constructor {
        mixin ThrowableTrait("oops")
    }
}

class Fatal : Error {
    constructor {
        mixin ThrowableTrait("fatal")
    }
}

// the static type does not tell whether the result is an Error
fn pick(fatal: Bool) -> mut Throwable {
    if fatal {
        return Fatal()
    }
    return Oops()
}

fn failWith(fatal: Bool) {
    throw pick(fatal)
}

class Thing {}

class Slot {
    var weak: Weak<Thing>? = null
}

// the references of the local variables are dropped exactly once, where a throwable goes to the catch
fn refcounting(stdout: mut PrintStream) {
    outer = Thing()
    weakOuter = Weak::<Thing>(outer)
    slot: mut Slot = Slot()
    // the throw is the first statement of the try block
    try {
        throw Oops()
    } catch e {
        stdout.println("caught: " + (e.message ?: "?"))
    }
    try {
        inner = Thing()
        set slot.weak = Weak::<Thing>(inner)
        throw pick(false)
    } catch e {
        stdout.println("caught: " + (e.message ?: "?"))
    }
    try {
        inner = Thing()
        set slot.weak = Weak::<Thing>(inner)
        failWith(false)
    } catch e {
        stdout.println("caught: " + (e.message ?: "?"))
    }
    if isNull(weakOuter.toStrongOrNull()) {
        stdout.println("BUG: the variable around the try blocks is gone")
    } else {
        stdout.println("the variable around the try blocks is still there")
    }
    if isNull(slot.weak!!.toStrongOrNull()) {
        stdout.println("the variable of the try block is gone")
    } else {
        stdout.println("BUG: the variable of the try block is still there")
    }
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    refcounting(stdout)

    // thrown by a function that the try block calls
    try {
        failWith(false)
        stdout.println("BUG: went on after the call")
    } catch e {
        stdout.println("thrown by a function, caught: " + (e.message ?: "?"))
    }

    // thrown in the try block itself
    try {
        stdout.println("throwing an Oops in the try block")
        throw Oops()
    } catch e {
        stdout.println("thrown in the try block, caught: " + (e.message ?: "?"))
    }

    try {
        local = "a local variable of the try block"
        stdout.println(local)
        throw pick(false)
    } catch e {
        stdout.println("thrown in the try block as a Throwable, caught: " + (e.message ?: "?"))
    }

    // thrown in a catch block: goes to the enclosing try
    try {
        try {
            throw Oops()
        } catch inner {
            stdout.println("inner catch: " + (inner.message ?: "?"))
            throw pick(false)
        }
    } catch outer {
        stdout.println("outer catch: " + (outer.message ?: "?"))
    }

    // an Error is not caught, though it is thrown in the try block itself and its static type is Throwable:
    // the program ends here
    try {
        try {
            stdout.println("throwing a Fatal in the try block, as a Throwable")
            throw pick(true)
        } catch inner {
            stdout.println("BUG: the inner catch caught an Error: " + (inner.message ?: "?"))
        }
        stdout.println("BUG: went on after the inner try")
    } catch outer {
        stdout.println("BUG: the outer catch caught an Error: " + (outer.message ?: "?"))
    }
    stdout.println("BUG: went on after the Error")
}

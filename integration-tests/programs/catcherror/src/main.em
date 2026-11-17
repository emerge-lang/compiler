package catcherror

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

class Fatal : Error {
    constructor {
        mixin ThrowableTrait("fatal")
    }
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    // an Error is not caught, also when it is thrown in the try block itself: the program ends here
    try {
        stdout.println("throwing a Fatal in the try block")
        throw Fatal()
    } catch e {
        stdout.println("BUG: caught an Error: " + (e.message ?: "?"))
    }
    stdout.println("BUG: went on after the Error")
}

package catchcast

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    strings: Array<String> = ["a", "b"]
    stringsAny: Any = strings

    // a CastError is an Error, it is not caught, also when the cast is in the try block itself: the program ends here
    try {
        stdout.println("casting an Array<String> to Array<S8> in the try block")
        bytes = stringsAny as Array<S8>
        stdout.println("BUG: the cast succeeded")
    } catch e {
        stdout.println("BUG: caught a CastError: " + (e.message ?: "?"))
    }
    stdout.println("BUG: went on after the CastError")
}

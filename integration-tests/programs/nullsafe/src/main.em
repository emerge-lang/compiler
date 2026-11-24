package nullsafe

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

class Box {
    p: String = init
    var counter: S32 = 0

    fn describe(self) -> String = "box " + self.p
    get fn length(self) -> S32 = 42
}

fn provide(present: Bool) -> Box? = if present Box("x") else null

fn traced(stdout: mut PrintStream, value: String) -> String {
    stdout.println("  evaluated argument")
    return value
}

fn appendTo(self: Box, stdout: mut PrintStream, suffix: String) {
    stdout.println("  invoked on " + self.p + suffix)
}

fn provideMut(present: Bool) -> mut Box? = if present Box("y") else null

fn tracedS32(stdout: mut PrintStream, value: S32) -> S32 {
    stdout.println("  evaluated value")
    return value
}

fn show(s: String?) -> String = s ?: "null"

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    // as a statement: neither the arguments are evaluated nor the function is invoked on null
    stdout.println("statement, null:")
    provide(false)?.appendTo(stdout, traced(stdout, "!"))
    stdout.println("statement, not null:")
    provide(true)?.appendTo(stdout, traced(stdout, "!"))

    // as an expression: evaluates to null on null
    stdout.println("expression, null: " + show(provide(false)?.describe()))
    stdout.println("expression, not null: " + show(provide(true)?.describe()))

    // returning a value type, which is boxed for the nullable result
    nullLength: S32? = provide(false)?.length
    length: S32? = provide(true)?.length
    stdout.println("getter, null: " + (if isNull(nullLength) "null" else nullLength.toString()))
    stdout.println("getter, not null: " + (if isNull(length) "null" else length.toString()))

    // assignment: the value isn't evaluated on null
    nullBox: mut Box? = provideMut(false)
    box: mut Box? = provideMut(true)
    stdout.println("assignment, null:")
    set nullBox?.counter = tracedS32(stdout, 1)
    stdout.println("assignment, not null:")
    set box?.counter = tracedS32(stdout, 1)
    stdout.println("  counter = " + box!!.counter.toString())
}

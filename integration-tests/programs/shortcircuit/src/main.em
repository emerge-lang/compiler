package shortcircuit

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

class Bar {
    p: String = init
}

fn show(b: Bool) -> String = if b "true" else "false"

fn traced(stdout: mut PrintStream, name: String, value: Bool) -> Bool {
    stdout.println("  evaluated " + name)
    return value
}

// the right-hand side is only evaluated where the left-hand side doesn't decide the result
fn shortCircuiting(stdout: mut PrintStream) {
    stdout.println("false and true:")
    r1 = traced(stdout, "lhs", false) and traced(stdout, "rhs", true)
    stdout.println("  = " + show(r1))

    stdout.println("true and true:")
    r2 = traced(stdout, "lhs", true) and traced(stdout, "rhs", true)
    stdout.println("  = " + show(r2))

    stdout.println("true or false:")
    r3 = traced(stdout, "lhs", true) or traced(stdout, "rhs", false)
    stdout.println("  = " + show(r3))

    stdout.println("false or false:")
    r4 = traced(stdout, "lhs", false) or traced(stdout, "rhs", false)
    stdout.println("  = " + show(r4))
}

// & and | on Bool always evaluate both sides
fn eager(stdout: mut PrintStream) {
    stdout.println("false & true:")
    r1 = traced(stdout, "lhs", false) & traced(stdout, "rhs", true)
    stdout.println("  = " + show(r1))

    stdout.println("true | false:")
    r2 = traced(stdout, "lhs", true) | traced(stdout, "rhs", false)
    stdout.println("  = " + show(r2))
}

fn isX(v: Bar?) -> String = if not isNull(v) and v.p == "x" "and: is x" else "and: not x"

fn isNullOrX(v: Bar?) -> String = if isNull(v) or v.p == "x" "or: null or x" else "or: neither"

fn firstIsOne(borrow arr: read Array<S32>) -> String = if arr.size > 0 and arr[0] == 1 "first is one" else "first is not one"

fn afterOrReturn(v: Bar?) -> String {
    not isNull(v) or return "or return: null"
    return "or return: " + v.p
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    shortCircuiting(stdout)
    eager(stdout)

    // smart casts in the right-hand side; the access would fail if it were evaluated
    stdout.println(isX(null))
    stdout.println(isX(Bar("x")))
    stdout.println(isX(Bar("y")))
    stdout.println(isNullOrX(null))
    stdout.println(isNullOrX(Bar("x")))
    stdout.println(isNullOrX(Bar("y")))
    stdout.println(afterOrReturn(null))
    stdout.println(afterOrReturn(Bar("z")))

    // the index access would throw if it were evaluated
    empty: Array<S32> = []
    one: Array<S32> = [1]
    stdout.println(firstIsOne(empty))
    stdout.println(firstIsOne(one))

    // bitwise on integers
    a: S32 = 12
    b: S32 = 10
    stdout.println("12 & 10 = " + (a & b).toString())
    stdout.println("12 | 10 = " + (a | b).toString())
    stdout.println("12 xor 10 = " + (a xor b).toString())
    stdout.println("not 12 = " + (not a).toString())
}

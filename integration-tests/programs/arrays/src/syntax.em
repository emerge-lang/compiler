package arrays

import emerge.std.io.PrintStream
fn makeInts(stdout: mut PrintStream) -> Array<S32> {
    stdout.println("makeInts called")
    return [4, 5, 6]
}

fn syntaxTests(stdout: mut PrintStream) {
    ints: Array<S32> = [1, 2, 3, 4]
    stdout.println(sumS32(ints[1..<3]).toString())
    stdout.println(ints[$ - 1].toString())
    stdout.println(sumS32(ints[0..<$ - 2]).toString())

    nested: Array<Array<S32>> = [[1, 2], [3, 4, 5]]
    stdout.println(sumS32(nested[1][1..<$]).toString())

    stdout.println(makeInts(stdout)[$ - 1].toString())

    foreach i in 2..<5 {
        stdout.println(i.toString())
    }

    r: mut _ = 1..<4
    r.popFront()
    stdout.println(sumS32(ints[r]).toString())

    foreach i in 5..<5 {
        stdout.println("never")
    }

    stdout.println(String.fromUtf8("Hello".utf8Data[1..<$ - 1]))

    m: mut Array<S32> = Array.new::<S32>(3, 0)
    set m[$ - 1] = 9
    stdout.println(m[2].toString())

    stdout.println("syntax done")
}

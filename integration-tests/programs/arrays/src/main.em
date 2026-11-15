package arrays

import emerge.std.io.PrintStream
import emerge.platform.StandardOut
import emerge.platform.World

import emerge.core.range.ArrayRange

class Holder {
    data: Array<S8> = init
}

class GenericHolder<T : Any> {
    value: T = init
}

fn sumS32(borrow arr: read Array<S32>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        set sum = sum + arr[i]
        set i = i + 1
    }
    return sum
}

fn countOutAny(borrow arr: read Array<out Any>) -> UWord {
    var n: UWord = 0
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        set n = n + 1
        set i = i + 1
    }
    return n
}

fn setIn(borrow arr: mut Array<in S8>) {
    set arr[0] = 65 as S8
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!
    ints: Array<S32> = [1, 2, 3, 4]
    stdout.println(sumS32(ints).toString())

    var buf = Array.new::<S32>(5, 7)
    set buf[2] = 100
    stdout.println(sumS32(buf).toString())
    stdout.println(buf.getOrPanic(2).toString())

    strs: Array<String> = ["a", "b", "c"]
    stdout.println(strs[1])
    stdout.println(countOutAny(strs).toString())
    stdout.println(countOutAny(ints).toString())

    bytes: mut Array<S8> = [66, 66]
    setIn(bytes)
    stdout.println(String(bytes))

    nested: mut Array<Array<S32>> = Array.new::<Array<S32>>(2, ints)
    set nested[1] = buf
    stdout.println(sumS32(nested[1]).toString())

    asAny: Any = ints
    if asAny is Array<S32> {
        stdout.println("is array")
    }

    var total: S32 = 0
    foreach x in ints {
        set total = total + x
    }
    stdout.println(total.toString())

    h = Holder([72, 105])
    stdout.println(String(h.data))

    gh = GenericHolder(ints)
    stdout.println(sumS32(gh.value).toString())

    target: mut Array<S32> = Array.new::<S32>(4, 0)
    Array.copy(ints, 1, target, 0, 3)
    stdout.println(sumS32(target).toString())


    hw: String = "Hello " + "World"
    stdout.println(hw)
    sliceTests(stdout)
    weakTests(stdout)
    nullableTests(stdout)
    syntaxTests(stdout)
    varianceTests(stdout)
    reifyTests(stdout)
    lastInts: Array<S32> = [1, 2, 3]
    lastInts.slice(1, 2)[1]
}

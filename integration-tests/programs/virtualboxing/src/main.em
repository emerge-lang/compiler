package virtualboxing

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream
import emerge.std.io.IOException

interface Maker<R> {
    fn make(self) -> R
}

class S32Maker : Maker<S32> {
    override fn make(self) -> S32 = 42
}

class UWordMaker : Maker<UWord> {
    override nothrow fn make(self) -> UWord = 7
}

class BoolMaker : Maker<Bool> {
    override fn make(self) -> Bool = true
}

class ArrayMaker : Maker<Array<S32>> {
    override fn make(self) -> Array<S32> = Array.new::<S32>(3, 5)
}

class NullMaker : Maker<S32?> {
    override fn make(self) -> S32? = null
}

class FailingMaker : Maker<S32> {
    override fn make(self) -> S32 {
        throw MakeFailed()
    }
}

class MakeFailed : IOException {
    constructor {
        mixin ThrowableTrait("make failed")
    }
}

interface Sink<T> {
    fn put(self: mut _, v: T)
}

class S32Sum : Sink<S32> {
    var sum: S32 = 0
    override fn put(self: mut _, v: S32) {
        set self.sum = self.sum + v
    }
}

fn makeGeneric<R>(m: Maker<R>) -> R = m.make()

fn putTwice<T>(borrow sink: mut Sink<T>, v: T) {
    sink.put(v)
    sink.put(v)
}

fn tryMake(stdout: mut PrintStream, m: Maker<S32>) {
    try {
        stdout.println(m.make().toString())
    } catch e {
        stdout.println("caught: " + (e.message ?: "?"))
    }
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    stdout.println(makeGeneric(S32Maker()).toString())
    stdout.println((makeGeneric(UWordMaker()) + 1).toString())
    stdout.println(makeGeneric(BoolMaker()).toString())

    arr = makeGeneric(ArrayMaker())
    stdout.println(arr.size.toString())
    stdout.println(arr[2].toString())

    stdout.println(makeGeneric(NullMaker())?.toString() ?: "null")

    tryMake(stdout, S32Maker())
    tryMake(stdout, FailingMaker())

    var i: S32 = 0
    while i < 100 {
        x = makeGeneric(S32Maker())
        y = makeGeneric(ArrayMaker())
        set i = i + 1
    }

    sum: mut S32Sum = S32Sum()
    putTwice(sum, 20)
    putTwice(sum, 1)
    stdout.println(sum.sum.toString())
}

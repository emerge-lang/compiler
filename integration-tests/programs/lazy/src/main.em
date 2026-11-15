package lazy

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream
import emerge.std.io.IOException

class Greeting : LazyInitializer<String> {
    name: String = init
    override fn computeValue(self: const _) -> String = "hello, " + self.name
}

class Constant<T : const Any?> : LazyInitializer<T> {
    v: T = init
    override fn computeValue(self: const _) -> T = self.v
}

class Failing : LazyInitializer<String> {
    override fn computeValue(self: const _) -> String {
        throw LazyFailed()
    }
}

class LazyFailed : IOException {
    constructor {
        mixin ThrowableTrait("initializer failed")
    }
}

class Holder {
    greeting: Lazy<String> = init
}

ITERATIONS: S32 = 101

globalLazy: Lazy<S32> = Lazy(Constant::<S32>(7))

fn tryFailing(stdout: mut PrintStream, borrow l: read Lazy<String>) {
    try {
        stdout.println(l.value)
    } catch e {
        stdout.println("caught: " + (e.message ?: "?"))
    }
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    g = Lazy(Greeting("world"))
    stdout.println(g.value)
    stdout.println(g.value)

    a = Lazy(Constant::<S32>(6 * 7))
    stdout.println(a.value.toString())
    stdout.println((a.value + 1).toString())

    n = Lazy(Constant::<String?>(null))
    stdout.println(n.value ?: "was null")
    stdout.println(n.value ?: "was null again")


    f = Lazy(Failing())
    tryFailing(stdout, f)
    tryFailing(stdout, f)

    stdout.println(globalLazy.value.toString())

    var i: S32 = 0
    while i < ITERATIONS {
        l = Lazy(Greeting("loop"))
        x = l.value
        y = l.value
        z = Lazy(Constant::<S32>(i))
        w = z.value
        set i = i + 1
    }

    h: const Holder = Holder(Lazy(Greeting("holder")))
    stdout.println(h.greeting.value)
    stdout.println(h.greeting.value)
}

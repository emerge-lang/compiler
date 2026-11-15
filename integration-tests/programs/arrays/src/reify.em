package arrays

import emerge.std.Printable
import emerge.std.io.PrintStream
import emerge.std.collections.ArrayList
import emerge.core.reflection.typeOf

class Tagged : Printable {
    tag: String = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        stream.put(self.tag)
    }
}

fn mk<T>(capture v: T) -> own Array<T> = Array.new::<T>(3, v)

fn lit<T>(capture a: T, capture b: T) -> own Array<T> = [a, b]

class GenHolder<T> {
    v: T = init

    fn arr(self) -> own Array<T> = Array.new::<T>(2, self.v)
}

fn holderOf<T>(capture v: T) -> own GenHolder<T> = GenHolder(v)

interface Maker<R> {
    fn make(self) -> Array<R>
}

class M<U> : Maker<U> {
    seed: U = init

    override fn make(self) -> Array<U> = Array.new::<U>(2, self.seed)
}

fn viaMaker(borrow maker: read Maker<S32>) -> S32 {
    arr = maker.make()
    return arr[0] + arr[1]
}

fn sumOfRange(capture arr: read Array<S32>) -> S32 {
    var sum: S32 = 0
    foreach x in arr {
        set sum = sum + x
    }
    return sum
}

class Weakly<T : Any> {
    weak: Weak<T> = init
}

fn weaken<T : Any>(capture v: T) -> own Weakly<T> = Weakly(Weak(v))

fn nameOf<T>() -> String = typeOf::<T>().firstComponent().baseType.canonicalName

fn reifyTests(stdout: mut PrintStream) {
    stdout.println("-- reify")
    ints = mk(1234 as S32)
    stdout.println(ints[0].toString())
    stdout.println(sumS32(ints).toString())

    maybeInts = mk::<S32?>(null)
    if isNull(maybeInts[1]) {
        stdout.println("null")
    }
    someInts = mk::<S32?>(7 as S32)
    stdout.println(someInts[2]!!.toString())

    bytes: Array<S8> = [1, 2]
    nestedBytes = mk(bytes)
    stdout.println(nestedBytes[0][1].toString())
    stdout.println(nestedBytes.size.toString())

    tagged = mk(Tagged("t"))
    tagged[1].printTo(stdout)
    stdout.println("")

    stdout.println("-- literal")
    stdout.println(sumS32(lit(5 as S32, 6 as S32)).toString())
    litMaybe = lit::<S32?>(null, 8 as S32)
    stdout.println(litMaybe[1]!!.toString())
    litBytes = lit(bytes, bytes)
    stdout.println(litBytes[1][0].toString())
    litTagged = lit(Tagged("a"), Tagged("b"))
    litTagged[1].printTo(stdout)
    stdout.println("")

    stdout.println("-- holder")
    h = GenHolder(5 as S32)
    stdout.println(sumS32(h.arr()).toString())
    h2 = holderOf(9 as S32)
    stdout.println(sumS32(h2.arr()).toString())

    stdout.println("-- maker")
    m = M(21 as S32)
    stdout.println(viaMaker(m).toString())

    stdout.println("-- range")
    stdout.println(sumOfRange(ints).toString())

    stdout.println("-- nested")
    nested = mk(ints)
    stdout.println(sumS32(nested[2]).toString())
    nestedMaybe = mk::<Array<S32?>>(someInts)
    stdout.println(nestedMaybe[0][2]!!.toString())

    stdout.println("-- arraylist")
    list: mut ArrayList<S32> = ArrayList::<S32>()
    list.add(40)
    list.add(2)
    var listSum: S32 = 0
    foreach x in list {
        set listSum = listSum + x
    }
    stdout.println(listSum.toString())

    stdout.println("-- weak")
    strong = Tagged("w")
    w = weaken(strong)
    stdout.println("weak ok")
    stdout.println("-- typeOf")
    stdout.println(typeOf::<Array<S32>>().firstComponent().arguments.size.toString())
    if typeOf::<S32?>().firstComponent().nullable {
        stdout.println("nullable")
    }
    stdout.println(nameOf::<S32>())
    stdout.println(nameOf::<Array<S8>>())
    if typeOf::<S32>().firstComponent().baseType.isSubtypeOf(typeOf::<Any>().firstComponent().baseType) {
        stdout.println("S32 is Any")
    }
    stdout.println("-- reify end")
}

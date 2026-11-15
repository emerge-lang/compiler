package arrays

import emerge.std.io.PrintStream
import emerge.core.range.Iterable
import emerge.std.collections.ArrayList

fn sumIterable(it: read Iterable<S32>) -> S32 {
    var sum: S32 = 0
    foreach x in it {
        set sum = sum + x
    }
    return sum
}

fn sliceOfGeneric<T : read Array<out Any?>>(capture a: T) -> T = a.slice(1, a.size)

fn sliceTests(stdout: mut PrintStream) {
    ints: Array<S32> = [1, 2, 3, 4]
    s = ints.slice(1, 3)
    stdout.println(s.size.toString())
    stdout.println(sumS32(s).toString())
    s2 = s.slice(1, 2)
    stdout.println(s2[0].toString())
    stdout.println(ints.slice(2, 2).size.toString())

    m: mut Array<S32> = Array.new::<S32>(5, 1)
    ms: mut _ = m.slice(2, 4)
    set ms[0] = 10
    stdout.println(m[2].toString())
    stdout.println(sumS32(m).toString())


    sAny: Any = s
    if sAny is Array<S32> {
        stdout.println("slice is array")
    }
    if sAny is Iterable<S32> {
        stdout.println("slice is iterable")
    }
    listAny: Any = ArrayList::<S32>()
    if listAny is Iterable<S32> {
        stdout.println("list is iterable")
    }
    if not (sAny is String) {
        stdout.println("slice is not a string")
    }
    stdout.println((sAny as Array<S32>).size.toString())
    stdout.println(sumIterable(s).toString())

    strs: Array<String> = ["a", "b", "c"]
    stdout.println(countOutAny(strs.slice(1, 3)).toString())
    stdout.println(strs.slice(1, 3)[1])

    nested: Array<Array<S32>> = [[1, 2], [3, 4, 5]]
    stdout.println(sumS32(nested[1]).toString())
    stdout.println(sumS32(nested.slice(1, 2)[0].slice(1, 3)).toString())
    stdout.println(countOutAny(nested).toString())

    gh = GenericHolder(s)
    stdout.println(sumS32(gh.value).toString())

    h = Holder("Hello".utf8Data.slice(1, 3))
    stdout.println(String(h.data))

    target: mut Array<S32> = Array.new::<S32>(4, 0)
    Array.copy(s, 0, target, 1, 2)
    stdout.println(sumS32(target).toString())
    Array.copy(target, 1, target, 2, 2)
    stdout.println(target[3].toString())

    maybe: Array<S32>? = s
    stdout.println(sumS32(maybe!!).toString())
    sz: UWord? = maybe?.size
    stdout.println(sz!!.toString())

    e: own _ = Array.new::<S32>(4, 2)
    es: mut _ = e.slice(0, 2)
    set es[0] = 7
    stdout.println(sumS32(es).toString())

    stdout.println(sumS32(sliceOfGeneric(ints)).toString())

    stdout.println("slices done")
}

package arrays

import emerge.std.io.PrintStream
class MaybeHolder {
    var data: Array<S32>? = null
}

fn maybeArray(give: Bool) -> Array<S32>? {
    if give {
        return [10, 20, 30]
    }
    return null
}

fn sizeOrZero(borrow arr: read Array<S32>?) -> UWord = arr?.size ?: 0

fn identity<T>(x: T) -> T = x

fn countNulls(borrow arr: read Array<out Any?>) -> UWord {
    var n: UWord = 0
    var i: UWord = 0
    while i < arr.size {
        if isNull(arr[i]) {
            set n = n + 1
        }
        set i = i + 1
    }
    return n
}

fn nullableTests(stdout: mut PrintStream) {
    n: Array<S32>? = null
    if isNull(n) {
        stdout.println("null array is null")
    }
    stdout.println(sizeOrZero(n).toString())
    stdout.println(sizeOrZero(maybeArray(true)).toString())
    stdout.println(sizeOrZero(maybeArray(false)).toString())

    given = maybeArray(true)
    stdout.println(sumS32(given!!).toString())
    fallback: Array<S32> = maybeArray(false) ?: [1, 1]
    stdout.println(sumS32(fallback).toString())

    h: mut MaybeHolder = MaybeHolder()
    stdout.println(sizeOrZero(h.data).toString())
    set h.data = [4, 5]
    stdout.println(sumS32(h.data!!).toString())
    set h.data = null
    stdout.println(sizeOrZero(h.data).toString())

    asAny: Any? = opaque::<Any?>(n)
    if isNull(asAny) {
        stdout.println("boxed null array is null")
    }
    asAny2: Any? = opaque::<Any?>(given)
    if asAny2 is Array<S32> {
        stdout.println("boxed non-null array is an array")
    }
    back: Array<S32>? = asAny2 as? Array<S32>
    stdout.println(sizeOrZero(back).toString())

    viaGenericNull: Array<S32>? = identity(n)
    stdout.println(sizeOrZero(viaGenericNull).toString())
    viaGeneric: Array<S32>? = identity(given)
    stdout.println(sizeOrZero(viaGeneric).toString())

    sub: Array<S32> = [7, 8]
    nested: mut Array<Array<S32>?> = [sub, null, sub]
    stdout.println(countNulls(nested).toString())
    stdout.println(sizeOrZero(nested[1]).toString())
    stdout.println(sumS32(nested[2]!!).toString())
    set nested[0] = null
    stdout.println(countNulls(nested).toString())

    uninit: Array<Array<S32>?> = Array.new::<Array<S32>?>(3, null)
    stdout.println(countNulls(uninit).toString())

    stdout.println("nullable done")
}

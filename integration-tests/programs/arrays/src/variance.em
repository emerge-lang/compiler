package arrays

import emerge.std.Printable
import emerge.std.io.PrintStream
import emerge.core.range.Iterable

class Named : Printable {
    name: String = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        stream.put(self.name)
    }
}

fn printBoundedT<T : Printable>(stdout: mut PrintStream, borrow arr: read Array<T>) {
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        x.printTo(stdout)
        stdout.put(" ")
        set i = i + 1
    }
    stdout.println("")
}

fn printOutPrintable(stdout: mut PrintStream, borrow arr: read Array<out Printable>) {
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        x.printTo(stdout)
        stdout.put(" ")
        set i = i + 1
    }
    stdout.println("")
}

fn printOutNullablePrintable(stdout: mut PrintStream, borrow arr: read Array<out Printable?>) {
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        x!!.printTo(stdout)
        stdout.put(" ")
        set i = i + 1
    }
    stdout.println("")
}

fn printOutNullableNamed(stdout: mut PrintStream, borrow arr: read Array<out Named?>) {
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        x!!.printTo(stdout)
        stdout.put(" ")
        set i = i + 1
    }
    stdout.println("")
}

fn sumOutNullableS32(borrow arr: read Array<out S32?>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        x: S32? = arr[i]
        set sum = sum + x!!
        set i = i + 1
    }
    return sum
}

fn sumOutS32(borrow arr: read Array<out S32>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        set sum = sum + arr[i]
        set i = i + 1
    }
    return sum
}

fn sumBoundedNullable<T : S32?>(borrow arr: read Array<T>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        x: S32? = arr[i]
        set sum = sum + x!!
        set i = i + 1
    }
    return sum
}

fn printNestedIterables(stdout: mut PrintStream, borrow arr: read Array<out Iterable<S8>>) {
    var i: UWord = 0
    while i < arr.size {
        foreach b in arr[i] {
            b.printTo(stdout)
            stdout.put(" ")
        }
        stdout.put("| ")
        set i = i + 1
    }
    stdout.println("")
}

fn putIn(borrow arr: mut Array<in S32>) {
    set arr[0] = 42
}

fn literalBounded<T : Printable>(stdout: mut PrintStream, capture a: T, capture b: T) {
    arr: Array<T> = [a, b]
    printBoundedT(stdout, arr)
}

fn sumBoundedAsS32<T : Printable>(borrow arr: read Array<T>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        set sum = sum + (x as S32)
        set i = i + 1
    }
    return sum
}

fn sumOutPrintableAsS32(borrow arr: read Array<out Printable>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        set sum = sum + (x as S32)
        set i = i + 1
    }
    return sum
}

fn sumOutNullablePrintableAsS32(borrow arr: read Array<out Printable?>) -> S32 {
    var sum: S32 = 0
    var i: UWord = 0
    while i < arr.size {
        x = arr[i]
        set sum = sum + (x!! as S32)
        set i = i + 1
    }
    return sum
}

fn literalBoundedSum<T : Printable>(capture a: T, capture b: T) -> S32 {
    arr: Array<T> = [a, b]
    return sumBoundedAsS32(arr)
}

fn makeGeneric<T : Printable>(capture v: T) -> own Array<T> = Array.new::<T>(2, v)

fn varianceTests(stdout: mut PrintStream) {
    stdout.println("-- variance")
    ints: Array<S32> = [11, 22, 33]
    stdout.println(sumBoundedAsS32(ints).toString())
    stdout.println(sumOutPrintableAsS32(ints).toString())
    stdout.println(sumOutNullablePrintableAsS32(ints).toString())
    stdout.println(sumOutNullableS32(ints).toString())
    stdout.println(sumOutS32(ints).toString())
    stdout.println(sumBoundedNullable(ints).toString())

    boxed: Array<S32?> = [1, 2, 3]
    stdout.println(sumOutNullableS32(boxed).toString())
    stdout.println(sumOutNullablePrintableAsS32(boxed).toString())

    first: Array<S8> = [1, 2]
    second: Array<S8> = [3]
    nested: Array<Array<S8>> = [first, second]
    printNestedIterables(stdout, nested)

    names: Array<Named> = [Named("ann"), Named("bob")]
    printBoundedT(stdout, names)
    printOutPrintable(stdout, names)
    printOutNullablePrintable(stdout, names)
    printOutNullableNamed(stdout, names)

    stdout.println("-- in")
    rawTarget: mut Array<S32> = [0, 5]
    putIn(rawTarget)
    stdout.println(sumS32(rawTarget).toString())
    anyTarget: mut Array<Any> = Array.new::<Any>(3, 0 as S32)
    putIn(anyTarget)
    stdout.println((anyTarget[0] as S32).toString())

    stdout.println("-- literal")
    stdout.println(literalBoundedSum(1 as S32, 2 as S32).toString())
    literalBounded(stdout, Named("cid"), Named("dan"))

    stdout.println("-- copy")
    copyInts: Array<S32> = [7, 8, 9]
    copyAny: mut Array<Any> = Array.new::<Any>(3, 0 as S32)
    Array.copy::<S32>(copyInts, 0, copyAny, 0, 3)
    stdout.println((copyAny[0] as S32).toString())
    stdout.println((copyAny[2] as S32).toString())

    nullableSource: Array<S32?> = [100, null, 300]
    nullableDest: mut Array<S32?> = Array.new::<S32?>(3, null)
    Array.copy::<S32?>(nullableSource, 0, nullableDest, 0, 3)
    stdout.println(nullableDest[0]!!.toString())
    if isNull(nullableDest[1]) {
        stdout.println("null")
    }
    stdout.println(nullableDest[2]!!.toString())

    byteSource: Array<S8> = [72, 105, 33]
    byteDest: mut Array<S8> = Array.new::<S8>(3, 0 as S8)
    Array.copy(byteSource, 0, byteDest, 0, 3)
    stdout.println(String(byteDest))

    stdout.println("-- generic creation probe")
    created = makeGeneric(1234 as S32)
    stdout.println(created[0].toString())
    stdout.println("-- variance end")
}

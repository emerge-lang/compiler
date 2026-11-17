package smartcasts

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

interface Foo {}

class Bar : Foo {
    p: String = init

    fn describe(self) -> String = "a bar with p = " + self.p
}

class Baz : Foo {}

fn produce(bar: Bool) -> Foo = if bar Bar("tadaaa") else Baz()

fn takeBar(b: Bar) -> String = "takeBar(" + b.p + ")"

fn fieldOrElse(v: Foo) -> String {
    if v is Bar {
        return "field: " + v.p
    } else {
        return "not a bar"
    }
}

fn generic<T>(v: T) -> String {
    if v is Bar {
        return "generic: " + v.p
    }
    return "generic: not a bar"
}

fn plusOne(v: Any) -> String {
    if v is S32 {
        return "S32 + 1 = " + (v + 1).toString()
    }
    return "not an S32"
}

fn arraySize(v: Any) -> String {
    if v is Array<S8> {
        return "array of " + v.size.toString() + " elements"
    }
    return "not an array"
}

fn notNull(v: S32?) -> S32 = v!! * 2

fn afterStrictCast(v: Foo) -> String {
    v as Bar
    return "after strict cast: " + v.p
}

fn isNullFalse(v: S32?) -> String {
    if isNull(v) {
        return "isNull: null"
    } else {
        return "isNull: S32 + 1 = " + (v + 1).toString()
    }
}

fn isNullFalseField(v: Bar?) -> String {
    if isNull(v) {
        return "isNull: null"
    } else {
        return "isNull: " + v.p
    }
}

fn afterStrictCastToS32(v: Any) -> S32 {
    v as S32
    return v + 1
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    // the program in test-project: a field of an interface variable refined to a class
    v = produce(true)
    if v is Bar {
        stdout.println("Is a bar; p = " + v.p)
        stdout.println(v.describe())
        stdout.println(takeBar(v))
    } else {
        stdout.println("Not a bar")
    }

    stdout.println(fieldOrElse(produce(true)))
    stdout.println(fieldOrElse(produce(false)))

    // T & Bar
    stdout.println(generic(produce(true)))
    stdout.println(generic::<Any>(3))

    // unboxing
    stdout.println(plusOne(41))
    stdout.println(plusOne("41"))
    bytes: Array<S8> = [1, 2, 3]
    stdout.println(arraySize(bytes))
    stdout.println(arraySize("abc"))
    stdout.println("S32? !! * 2 = " + notNull(21).toString())

    // the refinement ends with a new value
    var w = produce(true)
    if w is Bar {
        stdout.println("w before: " + w.p)
        set w = produce(false)
        stdout.println("w after: " + fieldOrElse(w))
    }

    stdout.println(afterStrictCast(produce(true)))
    stdout.println("after strict cast to S32: " + afterStrictCastToS32(41).toString())
    stdout.println(isNullFalse(41))
    stdout.println(isNullFalse(null))
    stdout.println(isNullFalseField(Bar("tadaaa")))
    stdout.println(isNullFalseField(null))
}

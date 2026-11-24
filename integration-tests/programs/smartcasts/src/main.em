package smartcasts

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

interface Foo : NonToken {}

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

fn safeCastNonNull(v: Foo) -> String {
    if isNull(v as? Bar) {
        return "safe cast: not a bar"
    } else {
        return "safe cast: " + v.p
    }
}

fn earlyReturn(v: Bar?) -> String {
    if isNull(v) {
        return "early return: null"
    }
    return "early return: " + v.p
}

fn earlyReturnS32(v: S32?) -> S32 {
    if isNull(v) {
        return 0
    }
    return v + 1
}

fn afterNotNull(v: S32?) -> S32 {
    v!!
    return v + 1
}

fn coalesceOrReturn(v: Foo) -> String {
    (v as? Bar) ?: return "?: return: not a bar"
    return "?: return: " + v.p
}

fn bothNotNull(a: S32?, b: S32?) -> String {
    if isNull(a) or isNull(b) {
        return "or: one is null"
    }
    return "or: sum = " + (a + b).toString()
}

class Node {
    value: S32 = init
    next: Node? = init
}

fn sumOfList(start: Node?) -> S32 {
    var sum: S32 = 0
    var node = start
    while not isNull(node) {
        set sum = sum + node.value
        set node = node.next
    }
    return sum
}

class Wrapper {
    content: Foo = init
    next: Wrapper? = init
}

fn wrapperContent(w: Wrapper) -> String {
    if w.content is Bar {
        return "member: " + w.content.p
    }
    return "member: not a bar"
}

fn lastWrapper(w: Wrapper) -> Wrapper {
    var node = w
    while not isNull(node.next) {
        set node = node.next
    }
    return node
}

fn afterStrictCastToS32(v: Any) -> S32 {
    v as S32
    return v + 1
}

// the refinement holds in the rest of the loop body after a branch that continues or breaks
fn sumSkippingNulls(values: Array<S32?>) -> S32 {
    var sum: S32 = 0
    foreach v in values {
        if isNull(v) {
            continue
        }
        set sum = sum + v
    }
    return sum
}

fn sumUntilNull(values: Array<S32?>) -> S32 {
    var sum: S32 = 0
    foreach v in values {
        if isNull(v) {
            break
        }
        set sum = sum + v
    }
    return sum
}

// a break as the first statement of a do-while body leaves that loop, not the enclosing one
fn doWhileBreak() -> S32 {
    var iterations: S32 = 0
    while iterations < 2 {
        do {
            break
        } while true
        set iterations = iterations + 1
    }
    return iterations
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
    stdout.println(safeCastNonNull(produce(true)))
    stdout.println(safeCastNonNull(produce(false)))
    stdout.println(earlyReturn(Bar("tadaaa")))
    stdout.println(earlyReturn(null))
    stdout.println("early return S32: " + earlyReturnS32(41).toString())
    stdout.println("after !!: " + afterNotNull(41).toString())
    stdout.println(coalesceOrReturn(produce(true)))
    stdout.println(coalesceOrReturn(produce(false)))
    stdout.println(bothNotNull(40, 2))
    stdout.println(bothNotNull(40, null))
    if not (v is Bar) {
        stdout.println("not: not a bar")
    } else {
        stdout.println("not: " + v.p)
    }
    stdout.println("while: sum = " + sumOfList(Node(20, Node(20, Node(2, null)))).toString())
    wrappers = Wrapper(produce(false), Wrapper(produce(false), Wrapper(produce(true), null)))
    stdout.println(wrapperContent(wrappers))
    stdout.println(wrapperContent(lastWrapper(wrappers)))
    values: Array<S32?> = [20, null, 20, 2]
    stdout.println("continue: sum = " + sumSkippingNulls(values).toString())
    stdout.println("break: sum = " + sumUntilNull(values).toString())
    stdout.println("do-while break: iterations = " + doWhileBreak().toString())
}

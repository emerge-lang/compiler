package unions

import emerge.core.reflection.Type
import emerge.core.reflection.typeOf
import emerge.core.reflection.isSubtypeOf
import emerge.platform.StandardOut
import emerge.platform.World
import emerge.std.io.PrintStream

class Circle {
    radius: S32 = init
}

class Square {
    side: S32 = init
}

class Label {
    text: String = init
}

// exhaustive over the components, so no else is needed
fn area(s: Circle | Square) -> S32 = when s {
    is Circle -> s.radius * s.radius * 3
    is Square -> s.side * s.side
}

// a value type among the components is boxed; a union in a branch covers its components
fn describe(v: Circle | Square | Label | S32) -> String = when v {
    is Circle | Square -> "shape of area " + area(v).toString()
    is Label -> "label " + v.text
    is S32 -> "number " + v.toString()
}

fn pick(n: S32) -> Circle | Square | Label | S32 = when {
    n == 0 -> Circle(2)
    n == 1 -> Square(3)
    n == 2 -> Label("hi")
    else -> n
}

// a nullable component makes the union nullable: `Circle | Label?` is `(Circle | Label)?`
fn maybe(n: S32) -> Circle | Label? = when {
    n == 0 -> Circle(1)
    n == 1 -> Label("tagged")
    else -> null
}

fn show(stdout: mut PrintStream, what: String, result: Bool) {
    stdout.println(what + ": " + (if result "yes" else "no"))
}

// the type arguments are known only at runtime
fn isEither<A, B>(borrow value: Any?) -> Bool = value is A | B

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    var n = 0
    while n < 5 {
        stdout.println(describe(pick(n)))
        set n = n + 1
    }

    set n = 0
    while n < 3 {
        m = maybe(n)
        stdout.println(when m {
            null -> "nothing"
            is Circle -> "circle"
            is Label -> "label " + m.text
        })
        set n = n + 1
    }

    // runtime checks against union types
    square: Any = Square(4)
    label: Any = Label("no")
    number: Any = 7
    show(stdout, "Square is Circle | Square", square is Circle | Square)
    show(stdout, "Label is Circle | Square", label is Circle | Square)
    show(stdout, "7 is Circle | S32", number is Circle | S32)
    show(stdout, "Square is Circle | S32", square is Circle | S32)
    show(stdout, "Square is A | B = Circle | Square", isEither::<Circle, Square>(square))
    show(stdout, "Label is A | B = Circle | Square", isEither::<Circle, Square>(label))
    if square is Circle | Square {
        stdout.println("smart cast: area " + area(square).toString())
    }

    // reified union types
    stdout.println(typeOf::<Circle | Square>().toString())
    stdout.println(typeOf::<Circle | Label?>().toString())
    show(stdout, "Circle is below Circle | Square", typeOf::<Circle>().isSubtypeOf(typeOf::<Circle | Square>()))
    show(stdout, "Circle | Square is below Circle", typeOf::<Circle | Square>().isSubtypeOf(typeOf::<Circle>()))
    show(stdout, "Circle | Square is below Circle | Square | Label", typeOf::<Circle | Square>().isSubtypeOf(typeOf::<Circle | Square | Label>()))
}

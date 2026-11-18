package whenexhaustive

import emerge.platform.StandardOut
import emerge.platform.World

// module-private, so the compiler knows all of the subtypes
interface Shape : NonToken {}

interface Polygon : Shape {}

class Circle : Shape {
    radius: S32 = init
}

class Square : Polygon {
    side: S32 = init
}

class Triangle : Polygon {}

fn produce(n: S32) -> Shape? = when {
    n == 0 -> Circle(2)
    n == 1 -> Square(3)
    n == 2 -> Triangle()
    else -> null
}

// exhaustive, used as a value: no else needed
fn describe(s: Shape) -> String = when s {
    is Circle -> "circle with radius " + s.radius.toString()
    is Square -> "square with side " + s.side.toString()
    is Triangle -> "triangle"
}

// an intermediate interface covers all of its subtypes
fn kind(s: Shape) -> String = when s {
    is Polygon -> "polygon"
    is Circle -> "round"
}

// a null branch covers null
fn describeNullable(s: Shape?) -> String = when s {
    null -> "nothing"
    is Circle -> "circle"
    is Polygon -> "polygon: " + describe(s)
}

// all branches return
fn sides(s: Shape) -> S32 {
    when s {
        is Circle -> return 0
        is Square -> return 4
        is Triangle -> return 3
    }
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    var n = 0
    while n < 4 {
        shape = produce(n)
        stdout.println(describeNullable(shape))
        if not isNull(shape) {
            stdout.println(describe(shape) + " is " + kind(shape) + " with " + sides(shape).toString() + " sides")
        }
        set n = n + 1
    }
}

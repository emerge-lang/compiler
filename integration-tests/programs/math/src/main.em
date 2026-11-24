package math

import emerge.platform.World
import emerge.platform.StandardOut
import emerge.platform.panic

export fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    assert(( 5 as S8).pow(0) == 1)
    assert(( 5 as S8).pow(1) == 5)
    assert(( 5 as S8).pow(2) == 25)
    assert((-2 as S8).pow(2) == 4)
    assert((-2 as S8).pow(3) == -8)
    assert(( 5 as U8).pow(0) == 1)
    assert(( 5 as U8).pow(1) == 5)
    assert(( 5 as U8).pow(2) == 25)

    assert(( 5 as S16).pow(0) == 1)
    assert(( 5 as S16).pow(1) == 5)
    assert(( 5 as S16).pow(2) == 25)
    assert((-2 as S16).pow(2) == 4)
    assert((-2 as S16).pow(3) == -8)
    assert(( 5 as U16).pow(0) == 1)
    assert(( 5 as U16).pow(1) == 5)
    assert(( 5 as U16).pow(2) == 25)

    assert(( 5 as S32).pow(0) == 1)
    assert(( 5 as S32).pow(1) == 5)
    assert(( 5 as S32).pow(2) == 25)
    assert((-2 as S32).pow(2) == 4)
    assert((-2 as S32).pow(3) == -8)
    assert(( 5 as U32).pow(0) == 1)
    assert(( 5 as U32).pow(1) == 5)
    assert(( 5 as U32).pow(2) == 25)

    assert(( 5 as S64).pow(0) == 1)
    assert(( 5 as S64).pow(1) == 5)
    assert(( 5 as S64).pow(2) == 25)
    assert((-2 as S64).pow(2) == 4)
    assert((-2 as S64).pow(3) == -8)
    assert(( 5 as U64).pow(0) == 1)
    assert(( 5 as U64).pow(1) == 5)
    assert(( 5 as U64).pow(2) == 25)

    stdout.println("done")
}

private fn assert(v: Bool) {
    if not v {
        panic("Assertion failed")
    }
}
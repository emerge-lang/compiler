package hello

import emerge.platform.StandardOut
import emerge.platform.World

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!
    stdout.println("Hello, World!")
}

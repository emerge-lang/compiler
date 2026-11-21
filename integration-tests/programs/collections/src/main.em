package collections

import emerge.platform.World

export fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    exerciseHashMap(stdout)
}

fn exerciseHashMap(stdout: mut PrintStream) {
    var map = HashMap<String, S32>()

    println(map["foo"]?.toString() ?: "null")
    map["foo"] = 1
    println(map["foo"]?.toString() ?: "null")
    map["bar"] = 2
    println(map["bar"]?.toString() ?: "null")
    map["foo"] = 3
    println(map["foo"]?.toString() ?: "null")
}
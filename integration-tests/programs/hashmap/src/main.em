package hashmap

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.core.hash.JavaLikeHashAlgorithm
import emerge.core.utf8.codepoints
import emerge.std.collections.{Map, HashMap}

fn lookup(m: Map<String, String>, key: String) -> String {
    return m[key] ?: "<empty>"
}

fn main(world: mut World) {
    stdout = StandardOut.take(world)!!

    var m = HashMap::<String, String>(JavaLikeHashAlgorithm())
    set m["flo"] = "2"
    set m["tobi"] = "5"
    stdout.println(lookup(m, "flo"))
    stdout.println(lookup(m, "tobi"))
    stdout.println(lookup(m, "nobody"))

    set m["flo"] = "3"
    stdout.println(lookup(m, "flo"))
    stdout.println(m.size.toString())

    stdout.println(m.contains("tobi").toString())
    stdout.println(m.remove("tobi") ?: "<none>")
    stdout.println(m.contains("tobi").toString())
    stdout.println(m.remove("tobi") ?: "<none>")
    stdout.println(m.size.toString())

    var i: UWord = 0
    while i < 200 {
        set m["k" + i.toString()] = i.toString()
        set i = i + 1
    }
    stdout.println(m.size.toString())
    stdout.println(lookup(m, "k0"))
    stdout.println(lookup(m, "k123"))
    stdout.println(lookup(m, "k199"))
    stdout.println(lookup(m, "k200"))
    stdout.println(lookup(m, "flo"))

    foreach codepoint in "aä€😀".codepoints() {
        stdout.println(codepoint.toString())
    }
}

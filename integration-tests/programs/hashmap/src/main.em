package hashmap

import emerge.platform.StandardOut
import emerge.platform.World
import emerge.core.hash.JavaLikeHashAlgorithm
import emerge.core.utf8.codepoints
import emerge.std.collections.{Map, HashMap, ArrayList}
import emerge.std.io.PrintStream

fn lookup(m: Map<String, String>, key: String) -> String {
    return m[key] ?: "<empty>"
}

// k10 .. k99, with the values 10 .. 99; after removing k0 .. k9 some buckets are left empty
fn ninetyEntries() -> HashMap<String, UWord> {
    var m = HashMap::<String, UWord>(JavaLikeHashAlgorithm())
    var i: UWord = 0
    while i < 100 {
        set m["k" + i.toString()] = i
        set i = i + 1
    }
    set i = 0
    while i < 10 {
        m.remove("k" + i.toString())
        set i = i + 1
    }
    return m
}

fn exerciseIteration(stdout: mut PrintStream) {
    var empty = HashMap::<String, UWord>(JavaLikeHashAlgorithm())
    var emptyRange = empty.asRange()
    stdout.println(emptyRange.size.toString())
    try {
        stdout.println(emptyRange.front.key)
    } catch e {
        stdout.println("front: " + (e.message ?: "?"))
    }
    try {
        stdout.println(emptyRange.back.key)
    } catch e {
        stdout.println("back: " + (e.message ?: "?"))
    }
    emptyRange.popFront()
    emptyRange.popBack()
    stdout.println(emptyRange.size.toString())

    // "a" goes into bucket 0 and "b" into bucket 15; removing "a" leaves bucket 0 empty, but not null
    var emptied = HashMap::<String, UWord>(JavaLikeHashAlgorithm())
    set emptied["a"] = 1 as UWord
    set emptied["b"] = 2 as UWord
    emptied.remove("a")
    foreach entry in emptied {
        stdout.println(entry.key + "=" + entry.value.toString())
    }

    var forwardKeys = ArrayList::<String>()
    var forwardSum: UWord = 0
    var forward = ninetyEntries().asRange()
    stdout.println(forward.size.toString())
    while forward.size > 0 {
        entry = forward.front
        forwardKeys.add(entry.key)
        set forwardSum = forwardSum + entry.value
        forward.popFront()
    }
    stdout.println(forwardKeys.size.toString())
    stdout.println(forwardSum.toString())

    var backwardKeys = ArrayList::<String>()
    var backward = ninetyEntries().asRange()
    while backward.size > 0 {
        backwardKeys.add(backward.back.key)
        backward.popBack()
    }
    var reversed = backwardKeys.size == forwardKeys.size
    var i: UWord = 0
    while reversed and i < forwardKeys.size {
        set reversed = forwardKeys[i].equals(backwardKeys[backwardKeys.size - 1 - i])
        set i = i + 1
    }
    stdout.println(reversed.toString())

    var bothEnds = ninetyEntries().asRange()
    var bothEndsCount: UWord = 0
    var bothEndsSum: UWord = 0
    while bothEnds.size > 0 {
        set bothEndsSum = bothEndsSum + bothEnds.front.value
        bothEnds.popFront()
        set bothEndsCount = bothEndsCount + 1
        if bothEnds.size > 0 {
            set bothEndsSum = bothEndsSum + bothEnds.back.value
            bothEnds.popBack()
            set bothEndsCount = bothEndsCount + 1
        }
    }
    stdout.println(bothEndsCount.toString())
    stdout.println(bothEndsSum.toString())
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

    exerciseIteration(stdout)
}

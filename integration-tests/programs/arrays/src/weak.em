package arrays

import emerge.std.io.PrintStream
class Thing {
    x: S32 = init
}

fn makeWeakArray(stdout: mut PrintStream) -> Weak<Array<S32>> {
    a: Array<S32> = [1, 2, 3, 4]
    w = Weak::<Array<S32>>(a.slice(1, 3))
    strong = w.toStrongOrNull()
    stdout.println(sumS32(strong!!).toString())
    return w
}

fn makeWeakThing(stdout: mut PrintStream) -> Weak<Thing> {
    t = Thing(7)
    w = Weak::<Thing>(t)
    strong = w.toStrongOrNull()
    stdout.println(strong!!.x.toString())
    return w
}

fn makeWeakThingNoAccess() -> Weak<Thing> {
    t = Thing(8)
    return Weak::<Thing>(t)
}

fn weakTests(stdout: mut PrintStream) {
    wn = makeWeakThingNoAccess()
    if isNull(wn.toStrongOrNull()) {
        stdout.println("weak thing without access is gone")
    }

    wa = makeWeakArray(stdout)
    if isNull(wa.toStrongOrNull()) {
        stdout.println("weak array is gone")
    }

    wt = makeWeakThing(stdout)
    if isNull(wt.toStrongOrNull()) {
        stdout.println("weak thing is gone")
    }

    kept: Array<S32> = [5, 6, 7]
    wk = Weak::<Array<S32>>(kept)
    stdout.println(sumS32(wk.toStrongOrNull()!!).toString())
    stdout.println(sumS32(kept).toString())

    stdout.println("weak done")
}

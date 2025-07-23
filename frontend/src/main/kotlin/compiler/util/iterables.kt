package compiler.util

inline fun <reified Sub> Sequence<Any?>.takeWhileIsInstance(): Sequence<Sub> {
    @Suppress("UNCHECKED_CAST")
    return takeWhile { it is Sub } as Sequence<Sub>
}

inline fun <T, reified S : T> Iterable<T>.partitionIsInstanceOf(): Pair<List<S>, List<T>> {
    val matches = ArrayList<S>(if (this is Collection) this.size else 10)
    val nonMatches = ArrayList<T>(matches.size)
    for (e in this) {
        if (e is S) {
            matches.add(e)
        } else {
            nonMatches.add(e)
        }
    }

    return Pair(matches, nonMatches)
}
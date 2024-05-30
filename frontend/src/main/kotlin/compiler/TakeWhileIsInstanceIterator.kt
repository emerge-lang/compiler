package compiler

inline fun <reified Sub> Sequence<Any?>.takeWhileIsInstance(): Sequence<Sub> {
    @Suppress("UNCHECKED_CAST")
    return takeWhile { it is Sub } as Sequence<Sub>
}
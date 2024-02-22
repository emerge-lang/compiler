package io.github.tmarsteel.emerge.backend.llvm

fun <T> Iterable<T>.indexed(): Iterable<Pair<Int, T>> = object : Iterable<Pair<Int, T>> {
    override fun iterator(): Iterator<Pair<Int, T>> = object : Iterator<Pair<Int, T>> {
        val inner = this@indexed.iterator()
        var index = 0

        override fun hasNext() = inner.hasNext()

        override fun next(): Pair<Int, T> {
            val element = Pair(index, inner.next())
            index += 1
            return element
        }
    }
}
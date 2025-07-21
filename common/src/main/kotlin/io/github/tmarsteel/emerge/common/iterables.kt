package io.github.tmarsteel.emerge.common

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

fun <A, B, C> zip(`as`: Iterable<A>, bs: Iterable<B>, cs: Iterable<C>) = object : Iterable<Triple<A, B, C>> {
    override fun iterator() = object : Iterator<Triple<A, B, C>> {
        private val asIt = `as`.iterator()
        private val bsIt = bs.iterator()
        private val csIt = cs.iterator()

        override fun hasNext(): Boolean {
            return asIt.hasNext() && bsIt.hasNext() && csIt.hasNext()
        }

        override fun next(): Triple<A, B, C> {
            return Triple(asIt.next(), bsIt.next(), csIt.next())
        }
    }
}

fun <A, B> zipNandNullable(`as`: Iterable<A>?, bs: Iterable<B>?): Iterable<Pair<A, B>>? {
    if (`as` == null) {
        check(bs == null)
        return null
    }
    check(bs != null)

    return `as`.zip(bs)
}


package compiler.parser.grammar.rule

class IteratorDuplicator<T>(val base: Iterator<T>) {
    private val cache = ArrayList<T>()
    private val mutex = Any()

    fun duplicate(): Iterator<T> = Instance()

    private inner class Instance : Iterator<T> {
        private var index = 0
        override fun hasNext(): Boolean {
            if (index < cache.size) {
                return true
            }

            synchronized(mutex) {
                if (index < cache.size) {
                    return true
                }

                return base.hasNext()
            }
        }

        override fun next(): T {
            if (index < cache.size) {
                return cache[index++]
            }

            synchronized(mutex) {
                if (index < cache.size) {
                    return cache[index++]
                }

                val next = base.next()
                cache.add(next)
                index++
                return next
            }
        }
    }
}
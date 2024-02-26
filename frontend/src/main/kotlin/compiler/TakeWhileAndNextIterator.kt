package compiler

/**
 * Like [TakeWhileSequence], but also yields the first element for which the predicate returns false.
 */
class TakeWhileAndNextIterator<T>(
    val base: Iterator<T>,
    val predicate: (T) -> Boolean,
) : Iterator<T> {
    private var state = State.PREDICATE_STILL_TRUE
    override fun hasNext(): Boolean = when(state) {
        State.PREDICATE_STILL_TRUE -> base.hasNext()
        State.STOPPED -> false
    }

    override fun next(): T {
        val next = when(state) {
            State.PREDICATE_STILL_TRUE -> base.next()
            State.STOPPED -> throw NoSuchElementException()
        }
        val predicateValue = predicate(next)
        state = when(state) {
            State.PREDICATE_STILL_TRUE -> if (predicateValue) State.PREDICATE_STILL_TRUE else State.STOPPED
            else -> throw RuntimeException("unreachable")
        }
        return next
    }

    private enum class State {
        PREDICATE_STILL_TRUE,
        STOPPED,
    }

    companion object {
        fun <T> Sequence<T>.takeWhileAndNext(predicate: (T) -> Boolean): Sequence<T> {
            return object : Sequence<T> {
                override fun iterator() = TakeWhileAndNextIterator(this@takeWhileAndNext.iterator(), predicate)
            }
        }
        fun <T> Iterable<T>.takeWhileAndNext(predicate: (T) -> Boolean): Sequence<T> {
            return object : Sequence<T> {
                override fun iterator() = TakeWhileAndNextIterator(this@takeWhileAndNext.iterator(), predicate)
            }
        }
    }
}
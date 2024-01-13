package compiler.lexer

import java.util.function.IntConsumer

class PositionTrackingCodePointIterator(val source: String, initialLineNumber: UInt = 1u, initialColumnNumber: UInt = 1u) {
    init {
        require(initialLineNumber >= 1u)
        require(initialColumnNumber >= 1u)
    }

    var currentLineNumber: UInt = initialLineNumber
        private set
    var currentColumnNumber: UInt = initialColumnNumber - 1u
        private set

    private var previousWasLinefeed = false
    private var nextAvailable = false
    private var next: Int = 0

    private val codePointSpliterator = source.codePoints().spliterator()
    private val setNextFn = IntConsumer {
        this.next = it
    }

    val hasNext: Boolean get() {
        if (nextAvailable) return true
        nextAvailable = codePointSpliterator.tryAdvance(setNextFn)
        return nextAvailable
    }

    fun next(): Int {
        if (!hasNext) {
            throw NoSuchElementException()
        }

        val localNext = next
        nextAvailable = false

        if (previousWasLinefeed) {
            currentLineNumber++
            currentColumnNumber = 1u
        } else {
            currentColumnNumber++
        }

        previousWasLinefeed = localNext == '\n'.code

        return localNext
    }
}
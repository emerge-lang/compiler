package compiler.lexer

import compiler.transact.TransactionalSequence
import java.util.Stack

@JvmInline
value class CodePoint(val value: Int) {
    val isWhitespace: Boolean get() = value == ' '.code || value == '\t'.code || value == '\r'.code
    val isLinefeed: Boolean get() = value == '\n'.code
    val isDigit: Boolean get() = Character.isDigit(value)
}

class SourceSpot(
    val codePointIndex: Int,
    val lineNumber: UInt,
    val columnNumber: UInt,
) {
    override fun toString() = "$lineNumber:$columnNumber [code point #$codePointIndex]"
}

/**
 * Like [TransactionalSequence], but hard-coded to [Int]/[CodePoint] to avoid boxing costs
 */
class PositionTrackingCodePointTransactionalSequence(
    val codePoints: IntArray,
    initialLineNumber: UInt = 1u,
    initialColumnNumber: UInt = 1u
) {
    constructor(code: String, initialLineNumber: UInt = 1u, initialColumnNumber: UInt = 1u) : this(
        code.codePoints().toArray(),
        initialLineNumber,
        initialColumnNumber,
    )

    init {
        require(initialLineNumber >= 1u)
        require(initialColumnNumber >= 1u)
    }

    var previousWasLinefeed: Boolean = false
    var currentPosition = SourceSpot(-1, initialLineNumber, initialColumnNumber - 1u)
        private set
    private val marks = Stack<SourceSpot>()

    @Throws(NoSuchElementException::class)
    fun nextOrThrow(): CodePoint {
        if (!hasNext) {
            throw NoSuchElementException()
        }

        val nextIndex = currentPosition.codePointIndex + 1
        val nextCodePoint = CodePoint(codePoints[nextIndex])

        val nextLineNumber: UInt
        val nextColumnNumber: UInt
        if (previousWasLinefeed) {
            nextLineNumber = currentPosition.lineNumber + 1u
            nextColumnNumber = 1u
        } else {
            nextLineNumber = currentPosition.lineNumber
            nextColumnNumber = currentPosition.columnNumber + 1u
        }
        previousWasLinefeed = nextCodePoint.isLinefeed

        currentPosition = SourceSpot(nextIndex, nextLineNumber, nextColumnNumber)
        return nextCodePoint
    }

    fun peek(): CodePoint? {
        if (!hasNext) {
            return null
        }

        return CodePoint(codePoints[currentPosition.codePointIndex + 1])
    }

    val hasNext: Boolean get() = currentPosition.codePointIndex < codePoints.lastIndex
    val nCodePointsRemaining: Int get() = codePoints.size - (currentPosition.codePointIndex + 1)

    fun mark() {
        marks.push(currentPosition)
    }

    fun commit() {
        marks.pop()
    }

    fun rollback() {
        currentPosition = marks.pop()
    }
}
package compiler.transact

import compiler.lexer.Token
import java.util.*

/**
 * A [Sequence] that is supposed to be consumed once with use of transactions (much like
 * [java.io.InputStream.mark] and [java.io.InputStream.reset]).
 *
 * The [Sequence] interface is not implemented because all of the methods would need to be overridden in order to
 * build in the transaction funcationality. If, at one point, that becomes reasonable, [Sequence] will be implemented.
 *
 * Each implementation of [TransactionalSequence] may define its own data structure to keep track of the current
 * position.
 */
abstract class TransactionalSequence<out ItemType, FallbackPointType : Position>(val items: List<ItemType>)
{
    // here follows the transaction management code
    private var markedPositions: Stack<FallbackPointType> = Stack()

    protected abstract var currentPosition: FallbackPointType

    protected abstract fun copyOfPosition(position: FallbackPointType): FallbackPointType

    /**
     * Returns the nextToken item from the source and advances the input pointer.
     * @return The nextToken item or `null` if the end of the sequence has been reached
     */
    open fun next(): ItemType? {
        if (items.lastIndex < currentPosition.sourceIndex)
        {
            return null
        }

        return items[currentPosition.sourceIndex++]
    }

    /** same as [next], but does not alter the state of the sequence */
    open fun peek(): ItemType? {
        if (items.lastIndex >= currentPosition.sourceIndex) {
            return items[currentPosition.sourceIndex]
        }
        else {
            return null
        }
    }

    open fun hasNext(): Boolean = items.lastIndex >= currentPosition.sourceIndex

    /**
     * Remembers the current location in the source. Use in conjunction with [commit] and [rollback].
     */
    fun mark()
    {
        markedPositions.push(copyOfPosition(currentPosition))
    }

    /**
     * Discards the last remembered location using [mark]. Invoke this method once you are sure that the characters
     * you have consumed so fare will be returned in a token.
     * @param nSteps The number of [mark] steps to erase.
     */
    fun commit(nSteps: Int = 1)
    {
        for (i in 0..nSteps - 1) markedPositions.pop()
    }

    /**
     * Resets the current source location to the last remembered location using [mark]. Use this if, after consuming
     * some characters, it has turned out that they cannot be evaluated just yet.
     * @param nSteps The number of [mark] steps to rollback
     */
    fun rollback(nSteps: Int = 1) {
        for (i in 0..nSteps - 1) currentPosition = markedPositions.pop()
    }

    /**
     * Marks the current position with [mark]. Then runs the code in the given function. If that code returns
     * gracefully, passes on the return value to the caller. If it throws an exception, rolls back the state to the
     * state marked before and rethrows the exception.
     * Transactions can be nested.
     * @return The result of the given function
     */
    fun <T> transact(txCode: TransactionReceiver.() -> T): T
    {
        mark()
        try
        {
            val retVal = txReceiver.txCode()
            commit()
            return retVal
        }
        catch (ex: Throwable)
        {
            rollback()
            throw ex
        }
    }

    /**
     * Invokes the given consumer on all items left in the sequence.
     */
    open fun forEachRemaining(consumer: (ItemType) -> Any?): Unit {
        while (hasNext()) consumer(next()!!)
    }

    /**
     * Invokes the given consumer on all items left in the sequence. The index always starts at 0.
     */
    open fun forEachRemainingIndexed(consumer: (Int, ItemType) -> Any?): Unit {
        var index = 0
        while (hasNext()) {
            consumer(index++, next()!!)
        }
    }

    /** Returns the remaining tokens in a list */
    open fun remainingToList(): List<ItemType> = items.subList(currentPosition.sourceIndex, items.lastIndex)

    inner class TransactionReceiver {
        fun next(): ItemType? = this@TransactionalSequence.next()
        fun <T> transact(txCode: TransactionReceiver.() -> T): T? = this@TransactionReceiver.transact(txCode)
    }
    private val txReceiver = TransactionReceiver()
}

class SimpleTransactionalSequence<T>(items: List<T>) : TransactionalSequence<T, Position>(items)
{
    override var currentPosition = Position(0)

    override fun copyOfPosition(position: Position) = Position(currentPosition.sourceIndex)
}
package compiler.transact

/**
 * A [TransactionalSequence] on a String that tracks line and column numbers.
 */
class SourceFileReader(code: String) : TransactionalSequence<Char, SourceFileReader.SourceLocation>(code.toList())
{
    override public var currentPosition: SourceLocation = SourceLocation(0, 1, 1)
        protected set

    override fun copyOfPosition(position: SourceLocation): SourceLocation
    {
        return SourceLocation(position.sourceIndex, position.lineNumber, position.columnNumber)
    }

    override fun next(): Char?
    {
        if (items.lastIndex < currentPosition.sourceIndex)
        {
            return null
        }

        val char = items[currentPosition.sourceIndex]

        if (currentPosition.sourceIndex > 0) {
            var previousChar = items[currentPosition.sourceIndex - 1]
            if (previousChar == '\n')
            {
                currentPosition.lineNumber++
                currentPosition.columnNumber = 1
            }
            else
            {
                currentPosition.columnNumber++
            }
        }

        currentPosition.sourceIndex++

        return char
    }

    fun next(nChars: Int) : String?
    {
        if (currentPosition.columnNumber + nChars - 1 > items.lastIndex)
        {
            return null
        }

        val buf = StringBuilder(nChars)
        for (i in 0..nChars - 1) {
            buf.append(next()!!)
        }
        return buf.toString()
    }


    class SourceLocation(
            sourceIndex: Int,
            var lineNumber: Int,
            var columnNumber: Int
    ) : Position(sourceIndex)
}
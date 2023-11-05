/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.transact

/**
 * A [TransactionalSequence] on a String that tracks line and column numbers.
 */
class SourceFileReader(code: String) : TransactionalSequence<Char, SourceFileReader.SourceLocation>(code.toList())
{
    override public var currentPosition: SourceLocation = SourceLocation(0,1, 1)
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
        if (currentPosition.sourceIndex + nChars - 1 > items.lastIndex)
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
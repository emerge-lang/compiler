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

package compiler.lexer

import java.nio.file.Files
import java.nio.file.Path

/**
 * Describes a source text (usually from a file, but ya never know!)
 */
interface SourceDescriptor
{
    val sourceLocation: String

    fun toLocation(sourceLine: Int, sourceColumn: Int): SourceLocation = SourceLocation(this, sourceLine, sourceColumn)
}

/**
 * A [SourceDescriptor] that is aware of the source text. That awareness can be used to create error messages that
 * cite erroneous parts of the code.
 */
abstract class SourceContentAwareSourceDescriptor : SourceDescriptor
{
    abstract val sourceLines: List<String>

    override fun toLocation(sourceLine: Int, sourceColumn: Int): SourceLocation
    {
        return SourceContentAwareSourceLocation(this, sourceLine, sourceColumn)
    }
}

/**
 * Describes a location within a source text (line + column)
 */
open class SourceLocation(
        open val sD: SourceDescriptor,
        open val sourceLine: Int,
        open val sourceColumn: Int
) {
    /** A string with source location, line number and column number */
    open val fileLineColumnText: String
        get() = "${sD.sourceLocation} on line $sourceLine, column $sourceColumn"

    /** @return a nice text representation of the source location */
    open fun illustrate() = fileLineColumnText

    /**
     * Returns a copy of this [SourceLocation] with the sourceColumn reduced by `n - 1`
     */
    open fun minusChars(n: Int): SourceLocation = SourceLocation(sD, sourceLine, sourceColumn - n + 1)

    override fun toString() = illustrate()

    companion object {
        val UNKNOWN: SourceLocation = object : SourceLocation(
            object : SourceDescriptor {
                override val sourceLocation = "UNKNOWN FILE"
            },
            -1,
            -1
        ) {
            override val fileLineColumnText = "UNKNOWN FILE"
            override fun minusChars(n: Int): SourceLocation = this
        }
    }
}

/**
 * Implements the pretty-print of erroneous source code (like the java compiler does, e.g.)
 */
open class SourceContentAwareSourceLocation(
        override val sD: SourceContentAwareSourceDescriptor,
        sourceLine: Int,
        sourceColumn: Int
): SourceLocation(sD, sourceLine, sourceColumn)
{
    override fun minusChars(n: Int): SourceLocation = SourceContentAwareSourceLocation(sD, sourceLine, sourceColumn - n + 1)

    override fun illustrate(): String {
        val line = sD.sourceLines[sourceLine - 1]

        return super.illustrate() + "\n" +
            "-".repeat(50) + "\n\n" +
            "  " + line + "\n" +
            "  " + " ".repeat(sourceColumn - 1) + "^\n" +
            "-".repeat(50)
    }

    fun illustrateWithExcerpt(): String {
        val lines = sD.sourceLines

        val startLine = if(sourceLine < 3) 1 else sourceLine - 2
        val endLine = Math.min(startLine + 5, lines.size)

        val excerptLines = lines.subList(startLine - 1, endLine - 1)
        val commonLeadingWhitespace = excerptLines
                .map { line -> line.length - line.trimStart(IsWhitespace).length }
                .min()!!

        val trimmedExcerptLines = excerptLines.map { it.substring(commonLeadingWhitespace) }
        val targetLineIndexInExcerpt = if (sourceLine < 3) sourceLine else startLine + 2

        val out = StringBuffer()

        out.append(super.illustrate())
        out.append('\n')
        out.append("-".repeat(50))
        out.append('\n')

        trimmedExcerptLines.forEachIndexed { index, line ->
            out.append("  ")
            out.append(line)
            out.append('\n')

            if (index + 1 == targetLineIndexInExcerpt)
            {
                out.append("  ")
                out.append(" ".repeat(Math.max(0, sourceColumn - 1)))
                out.append("^\n")
            }
        }

        out.append("-".repeat(50))

        return out.toString()
    }
}

class PathSourceDescriptor(val path: Path) : SourceContentAwareSourceDescriptor()
{
    override val sourceLocation = path.toString()

    override val sourceLines: List<String> by lazy { Files.readAllLines(path) }
}
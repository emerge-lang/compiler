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

package compiler.diagnostic

import compiler.lexer.SourceFile
import compiler.lexer.Span
import compiler.util.groupRunsBy
import kotlin.math.min

data class SourceHint(
    val span: Span,
    val description: String?,
    val relativeOrderMatters: Boolean = false,
    val nLinesContext: UInt = 1u,
)

fun illustrateSourceLocations(locations: Collection<Span>): String = illustrateHints(locations.map { SourceHint(it, null) })
fun illustrateHints(vararg hints: SourceHint): String = illustrateHints(hints.toList())
fun illustrateHints(hints: List<SourceHint>): String {
    if (hints.isEmpty()) {
        throw IllegalArgumentException("No locations given to highlight")
    }
    hints.find { it.span.fromLineNumber != it.span.toLineNumber }?.let {
        throw NotImplementedError("Cannot highlight source locations that span multiple lines: ${it.span.fileLineColumnText}")
    }

    val hintGroups = hints
        .filter { it.relativeOrderMatters }
        .groupRunsBy { it.span.sourceFile }
        .map { (file, hints) -> Pair(file, hints.toMutableList()) }
        .toMutableList()
    hints
        .filterNot { it.relativeOrderMatters }
        .forEach { unorderedHint ->
            var lastGroupOfFile = hintGroups.lastOrNull { it.first == unorderedHint.span.sourceFile }
            if (lastGroupOfFile == null) {
               lastGroupOfFile = Pair(unorderedHint.span.sourceFile, ArrayList())
               hintGroups.add(lastGroupOfFile)
            }
            lastGroupOfFile.second.add(unorderedHint)
        }

    val sb = StringBuilder()
    for ((file, hintsInGroup) in hintGroups) {
        sb.append(file)
        sb.append(":\n")
        buildIllustrationForSingleFile(file, hintsInGroup, sb)
    }
    return sb.toString()
}

private fun buildIllustrationForSingleFile(
    file: SourceFile,
    hints: Collection<SourceHint>,
    sb: StringBuilder,
) {
    val sourceLines = file.content.split('\n')
    hints.find { it.span.fromLineNumber > sourceLines.size.toUInt() }?.let {
        throw IllegalArgumentException("Source lines out of range: $it")
    }

    val hintsByLine = hints.groupBy { it.span.fromLineNumber }

    val lineNumbersToOutput = mutableSetOf<UInt>()
    for (hint in hints) {
        val desiredLine = hint.span.fromLineNumber
        lineNumbersToOutput.add(desiredLine)
        for (i in 1u .. hint.nLinesContext) {
            if (desiredLine > 2u) {
                lineNumbersToOutput.add(desiredLine - i)
            }
            if (desiredLine < sourceLines.size.toUInt()) {
                lineNumbersToOutput.add(desiredLine + i)
            }
        }
    }

    val lineNumbersToOutputSorted = lineNumbersToOutput.sorted()
    val lineCounterLength = min(3, lineNumbersToOutputSorted.max().toString(10).length)

    val linesToOutputWithNormalizedTabs: Map<UInt, String> = lineNumbersToOutputSorted.associateWith {
        sourceLines[(it - 1u).toInt()].replace("\t", "    ")
    }

    val commonNumberOfLeadingSpaces = linesToOutputWithNormalizedTabs.values.minOf { it.takeWhile { char -> char == ' ' }.length }

    fun StringBuilder.appendUnnumberedLinePrefix() {
        repeat(lineCounterLength + 1) {
            append(' ')
        }
        append("|  ")
    }

    fun StringBuilder.appendHintDescriptionLine(hint: SourceHint, isAbove: Boolean) {
        appendUnnumberedLinePrefix()
        repeat(hint.span.fromColumnNumber.toInt() - commonNumberOfLeadingSpaces - 1) {
            append(' ')
        }
        val nCols = (hint.span.toColumnNumber - hint.span.fromColumnNumber).toInt() + 1
        val pointerWidth = 2 // width of the pointer emojis in monospace fonts
        val nSwigglesTotal = nCols - pointerWidth
        val nSgwigglesBefore = nSwigglesTotal / 2
        val nSgiwgglesAfter = nSwigglesTotal - nSgwigglesBefore
        check(nSgwigglesBefore + pointerWidth + nSgiwgglesAfter == nCols)
        repeat(nSgwigglesBefore) {
            append('~')
        }
        if (isAbove) {
            append("\uD83D\uDC47") // 👇
        } else {
            append("\uD83D\uDC46") // 👆
        }
        repeat(nSgiwgglesAfter) {
            append('~')
        }

        if (hint.description != null) {
            append(' ')
            append(hint.description)
        }
        append('\n')
    }

    sb.appendUnnumberedLinePrefix()
    sb.append('\n')

    val lineSkippingIndicatorLine = "...".padStart(lineCounterLength, ' ') + "\n"

    for (index in 0 .. lineNumbersToOutputSorted.lastIndex) {
        val lineNumber = lineNumbersToOutputSorted[index]

        val hintsOnLine = hintsByLine[lineNumber] ?: emptyList()
        val hintAbove: SourceHint?
        val hintBelow: SourceHint?
        when (hintsOnLine.size) {
            0 -> {
                hintAbove = null
                hintBelow = null
            }
            1 -> {
                hintAbove = null
                hintBelow = hintsOnLine[0]
            }
            2 -> {
                hintAbove = hintsOnLine[0]
                hintBelow = hintsOnLine[1]
            }
            else -> {
                throw NotImplementedError("More than two hints per source line is not supported currently ($file, line $lineNumber)")
                // this would require a much more intricate layouting logic than what there is now
            }
        }

        hintAbove?.let { sb.appendHintDescriptionLine(it, true) }
        sb.append(lineNumber.toString(10).padStart(lineCounterLength, ' '))
        sb.append(" |  ")
        sb.append(linesToOutputWithNormalizedTabs[lineNumber]!!.substring(commonNumberOfLeadingSpaces))
        sb.append("\n")
        hintBelow?.let { sb.appendHintDescriptionLine(it, false) }

        if (index != lineNumbersToOutputSorted.lastIndex) {
            val nextLineNumber = lineNumbersToOutputSorted[index + 1]
            if (lineNumber + 1u != nextLineNumber) {
                // we are skipping some lines
                sb.append(lineSkippingIndicatorLine)
            }
        }
    }

    sb.appendUnnumberedLinePrefix()
    sb.append('\n')
}

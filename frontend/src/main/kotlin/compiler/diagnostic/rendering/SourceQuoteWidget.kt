package compiler.diagnostic.rendering

import compiler.diagnostic.SourceHint
import compiler.lexer.LexerSourceFile
import compiler.lexer.Span
import compiler.util.groupRunsBy
import java.util.Comparator.comparing

/**
 * A dynamically sized grid of monospaced characters. Simplifies layouting of ascii-art-like output
 * which gets exponentially difficult with layout complexity when you just concatenate chars to a string.
 */
class SourceQuoteWidget(
    val file: LexerSourceFile,
) {
    private val lines = file.content.split('\n').map(::TextSpan)

    private val singleLineHints = mutableMapOf<UInt, LinkedHashSet<SourceHint>>()
    private val multiLineHints = sortedSetOf<SourceHint>(comparing { it.span.fromLineNumber })

    fun addHint(hint: SourceHint) {
        require(hint.span.sourceFile == file)

        val fromLine = hint.span.fromLineNumber
        if (fromLine == hint.span.toLineNumber) {
            singleLineHints.computeIfAbsent(fromLine, { LinkedHashSet() }).add(hint)
        } else {
            multiLineHints.add(hint)
        }
    }

    private val lineNumbersToOutput: List<UInt> get() {
        val set = LineNumberSet(nTotalLines = lines.size.toUInt())
        singleLineHints.values.asSequence().flatten().forEach {
            set.addLineAndContext(it.span.fromLineNumber, it.nLinesContext)
        }
        multiLineHints.forEach {
            for (line in it.span.fromLineNumber .. it.span.toLineNumber) {
                set.addLineAndContext(line, it.nLinesContext)
            }
        }

        return set.sorted()
    }

    fun render(canvas: MonospaceCanvas) {
        canvas.assureOnBlankLine()

        canvas.append(TextSpan("$file:"))
        canvas.appendLineBreak()

        renderQuoteAndInlineHints(canvas)
        canvas.addColumnToLeftOfAllCurrentLines(TextAlignment.RIGHT) { line ->
            val lnText = line.markers.findInstanceOf<LogicalLineNumberMarker>()?.number?.toString() ?: ""
            TextSpan("$lnText | ")
        }
    }

    private fun renderQuoteAndInlineHints(canvas: MonospaceCanvas) {
        for (lineNumber in lineNumbersToOutput) {
            val lineText = lines[lineNumber.toInt() - 1]
            val hints = singleLineHints[lineNumber]
            val hintAbove: SourceHint?
            val hintsBelow: Iterable<SourceHint>?
            when (hints?.size) {
                null, 0 -> {
                    hintAbove = null
                    hintsBelow = emptySet()
                }
                1 -> {
                    hintAbove = null
                    hintsBelow = hints
                }
                else -> {
                    hintAbove = hints.first()
                    hintsBelow = hints.drop(1)
                }
            }
            hintAbove?.let {
                renderSingleLineHint(it, lineText, canvas, true)
            }

            canvas.append(lineText)
            canvas.addMarkerToCurrentLine(
                LogicalLineNumberMarker(lineNumber)
            )
            canvas.appendLineBreak()

            hintsBelow.forEach {
                renderSingleLineHint(it, lineText, canvas, false)
            }
        }
    }

    private fun renderSingleLineHint(
        hint: SourceHint,
        lineText: TextSpan,
        canvas: MonospaceCanvas,
        above: Boolean
    ) {
        val paddingLeftCellWidth = canvas.renderTargetInfo.computeCellWidth(lineText.substring(0, hint.span.fromColumnNumber.toInt() - 1))
        val markerCellWidth = canvas.renderTargetInfo.computeCellWidth(lineText.substring(hint.span.fromColumnNumber.toInt() - 1, hint.span.toColumnNumber.toInt()))
        val pointer = TextSpan(if (markerCellWidth == 1) {
            if (above) "v" else "^"
        } else {
            if (above) "\uD83D\uDC47" /*👇*/ else "\uD83D\uDC46" /*👆*/
        })

        val pointerWidth = canvas.renderTargetInfo.computeCellWidth(pointer)
        val swiggleWidth = markerCellWidth - pointerWidth
        val swiggleWidthBefore = swiggleWidth / 2
        val swiggleWidthAfter = swiggleWidth - swiggleWidthBefore
        check(swiggleWidthBefore + pointerWidth + swiggleWidthAfter == markerCellWidth)

        canvas.assureOnBlankLine()
        repeat(paddingLeftCellWidth) {
            canvas.append(spanPadding)
        }
        repeat(swiggleWidthBefore) {
            canvas.append(spanSwiggle)
        }
        canvas.append(pointer)
        repeat(swiggleWidthAfter) {
            canvas.append(spanSwiggle)
        }
        if (hint.description != null) {
            canvas.append(spanPadding)
            canvas.append(TextSpan(hint.description))
        }
        canvas.appendLineBreak()
    }

    companion object {
        private val spanPadding = TextSpan(" ")
        private val spanSwiggle = TextSpan("~")

        fun renderHintsFromMultipleFiles(canvas: MonospaceCanvas, vararg locations: Span) {
            renderHintsFromMultipleFiles(canvas, *locations.map { SourceHint(it, null) }.toTypedArray())
        }

        fun renderHintsFromMultipleFiles(canvas: MonospaceCanvas, vararg hints: SourceHint) {
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

            for ((file, hintsInGroup) in hintGroups) {
                val widget = SourceQuoteWidget(file)
                hintsInGroup.forEach(widget::addHint)
                widget.render(canvas)
            }
        }
    }
}


private class LineNumberSet(val nTotalLines: UInt, val ns: MutableSet<UInt> = mutableSetOf()) : Set<UInt> by ns {
    fun addLineAndContext(desiredLine: UInt, nContextLines: UInt) {
        for (i in 1u..nContextLines) {
            ns.add(desiredLine)

            if (desiredLine > 2u) {
                ns.add(desiredLine - i)
            }
            if (desiredLine < nTotalLines) {
                ns.add(desiredLine + i)
            }
        }
    }
}

private data class LogicalLineNumberMarker(val number: UInt)

private inline fun <reified T : Any> Iterable<Any>.findInstanceOf(): T? {
    for (e in this) {
        if (e is T) {
            return e
        }
    }

    return null
}
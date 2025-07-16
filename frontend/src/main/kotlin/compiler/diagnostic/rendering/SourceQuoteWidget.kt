package compiler.diagnostic.rendering

import compiler.diagnostic.Diagnostic
import compiler.diagnostic.SourceHint
import compiler.lexer.LexerSourceFile
import java.util.Comparator.comparing

/**
 * A dynamically sized grid of monospaced characters. Simplifies layouting of ascii-art-like output
 * which gets exponentially difficult with layout complexity when you just concatenate chars to a string.
 */
class SourceQuoteWidget(
    val file: LexerSourceFile,
) : MonospaceWidget {
    private val lines = file.content.split('\n').map { TextSpan(it, TextSpan.DEFAULT_STYLE) }

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

    override fun render(canvas: MonospaceCanvas) {
        canvas.assureOnBlankLine()

        canvas.append(TextSpan("$file:"))

        val quoteCanvas = canvas.createViewAppendingToBlankLine()
        renderQuoteAndInlineHints(quoteCanvas)
        quoteCanvas.addColumnToLeftOfAllCurrentLines(TextAlignment.LINE_END) { line ->
            val lnText = line.markers.findInstanceOf<LogicalLineNumberMarker>()?.number?.toString() ?: ""
            TextSpan("$lnText | ", canvas.theme.lineNumbers)
        }

        renderMultilineHints(quoteCanvas)
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
        if (lineText.content.isEmpty()) {
            // cannot highlight, it's very likely that hint.span == Span.UNKNOWN
            canvas.append(TextSpan("^ "))
            hint.description?.let(::TextSpan)?.let(canvas::append)
            canvas.appendLineBreak()
            return
        }

        val swiggleStyle = swiggleStyle(canvas, hint.severity)

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
        canvas.append(TextSpan(swiggleChar.repeat(swiggleWidthBefore), swiggleStyle))
        canvas.append(pointer)
        canvas.append(TextSpan(swiggleChar.repeat(swiggleWidthAfter), swiggleStyle))

        if (hint.description != null) {
            canvas.append(spanPadding)
            canvas.append(TextSpan(hint.description))
        }
        canvas.appendLineBreak()
    }

    private fun renderMultilineHints(canvas: MonospaceCanvas) {
        var referenceNumberCounter = 1
        for (multiLineHint in multiLineHints) {
            val hasDescription = multiLineHint.description != null
            val middleLine = multiLineHint.span.fromLineNumber + (multiLineHint.span.toLineNumber - multiLineHint.span.fromLineNumber) / 2u
            val referenceNumber = referenceNumberCounter
            if (hasDescription) {
                referenceNumberCounter++
            }

            val swiggleStyle = swiggleStyle(canvas, multiLineHint.severity)
            canvas.addColumnToLeftOfAllCurrentLines(TextAlignment.LINE_END) { _ -> TextSpan(" ") }
            canvas.addColumnToLeftOfAllCurrentLines(TextAlignment.CENTER) { canvasLine ->
                val ln = canvasLine.markers.findInstanceOf<LogicalLineNumberMarker>()?.number

                when {
                    ln == null -> TextSpan.EMPTY
                    ln == multiLineHint.span.fromLineNumber -> TextSpan("/", swiggleStyle)
                    ln == middleLine && hasDescription -> TextSpan("[${referenceNumber}]", swiggleStyle)
                    ln == multiLineHint.span.toLineNumber -> TextSpan("\\", swiggleStyle)
                    ln in multiLineHint.span.fromLineNumber..multiLineHint.span.toLineNumber -> TextSpan("|", swiggleStyle)
                    else -> TextSpan.EMPTY
                }
            }
        }

        multiLineHints.filter { it.description != null }.forEachIndexed { index, multiLineHint ->
            canvas.assureOnBlankLine()
            canvas.append(TextSpan("[${index + 1}]: ${multiLineHint.description}"))
        }
    }

    companion object {
        private val spanPadding = TextSpan(" ")
        private val swiggleChar = "~"
        private fun swiggleStyle(canvas: MonospaceCanvas, severity: Diagnostic.Severity) = when (severity) {
            Diagnostic.Severity.ERROR -> canvas.theme.sourceLocationPointerError
            Diagnostic.Severity.WARNING -> canvas.theme.sourceLocationPointerWarning
            Diagnostic.Severity.INFO -> canvas.theme.sourceLocationPointerInfo
            else -> TextSpan.DEFAULT_STYLE
        }
    }
}


private class LineNumberSet(val nTotalLines: UInt, val ns: MutableSet<UInt> = mutableSetOf()) : Set<UInt> by ns {
    fun addLineAndContext(desiredLine: UInt, nContextLines: UInt) {
        val start = (desiredLine - nContextLines).coerceAtLeast(1u)
        val end = (desiredLine + nContextLines).coerceAtMost(nTotalLines)
        for (i in start .. end) {
            ns.add(i)
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
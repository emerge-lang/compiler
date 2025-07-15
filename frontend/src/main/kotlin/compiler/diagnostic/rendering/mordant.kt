package compiler.diagnostic.rendering

import com.github.ajalt.mordant.rendering.Line as MordantLine
import com.github.ajalt.mordant.rendering.Lines as MordantLines
import com.github.ajalt.mordant.rendering.Span as MordantSpan

fun MonospaceCanvas.toMordantLines(): MordantLines {
    val sourceLinesIt = lines.iterator()
    val outputLines = ArrayList<MordantLine>()
    while (sourceLinesIt.hasNext()) {
        val sourceLine = sourceLinesIt.next()
        val mordantSpans = ArrayList<MordantSpan>(sourceLine.spans.size)
        for (sourceSpan in sourceLine.spans) {
            val wordsIt = sourceSpan.content.split(Regex("\\s")).iterator()
            while (wordsIt.hasNext()) {
                val word = wordsIt.next()
                if (word.isNotEmpty()) {
                    mordantSpans.add(MordantSpan.word(word, sourceSpan.style))
                }
                if (wordsIt.hasNext()) {
                    mordantSpans.add(MordantSpan.space(1))
                }
            }
        }

        outputLines.add(MordantLine(mordantSpans))
    }

    return MordantLines(outputLines)
}
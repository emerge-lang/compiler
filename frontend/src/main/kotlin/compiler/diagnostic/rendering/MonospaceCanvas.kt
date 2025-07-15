package compiler.diagnostic.rendering

interface MonospaceCanvas : AutoCloseable {
    val renderTargetInfo: RenderTargetInfo

    fun append(span: TextSpan)

    fun appendPartialLine(partialLine: Line) {
        partialLine.spans.forEach(::append)
    }

    fun appendLineBreak()

    fun assureOnBlankLine()

    fun addMarkerToCurrentLine(marker: Any)

    fun addColumnToLeftOfAllCurrentLines(
        alignment: TextAlignment,
        computeContent: (line: Line) -> TextSpan,
    )

    fun createViewAppendingToBlankLine(): MonospaceCanvas

    val lines: Sequence<Line>

    data class RenderTargetInfo(
        val tabWidth: Int,
    ) {
        fun computeCellWidth(span: TextSpan): Int {
            // simple heuristic; counting chars is over-simplified, and counting every char as width 1 is simplified as well
            // but because of all the complexity, most terminals determine char widths the same way and will even coerce smaller
            // graphemes (like emojis) to a larger space; so it works reasonably well to just copy the madness here...
            return span.content.chars()
                .map { charCode -> when (charCode) {
                    '\n'.code -> throw IllegalArgumentException("TextSpan contains linebreak")
                    '\t'.code -> tabWidth
                    else -> 1
                } }
                .sum()
        }

        fun alignInPlace(partialLine: MutableList<TextSpan>, toWidth: Int, alignment: TextAlignment) {
            var unpaddedWidth = 0
            for (span in partialLine) {
                unpaddedWidth += computeCellWidth(span)
            }
            if (unpaddedWidth == toWidth) {
                return
            }
            check(unpaddedWidth < toWidth)

            when (alignment) {
                TextAlignment.LINE_START -> {
                    partialLine.addLast(TextSpan(" ".repeat(toWidth - unpaddedWidth)))
                }
                TextAlignment.LINE_END -> {
                    partialLine.addFirst(TextSpan(" ".repeat(toWidth - unpaddedWidth)))
                }
                TextAlignment.CENTER -> {
                    val nPadding = toWidth - unpaddedWidth
                    val nBefore = nPadding / 2
                    val nAfter = nPadding - nBefore
                    partialLine.addFirst(TextSpan.whitespace(nBefore))
                    partialLine.addLast(TextSpan.whitespace(nAfter))
                }
            }
        }
    }

    interface Line {
        val spans: List<TextSpan>
        val markers: Set<Any>
        fun mark(marker: Any)
    }
}
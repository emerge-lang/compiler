package compiler.diagnostic.rendering

interface MonospaceCanvas : AutoCloseable {
    val renderTargetInfo: RenderTargetInfo

    fun append(span: TextSpan)

    fun appendLineBreak()

    fun assureOnBlankLine()

    fun addMarkerToCurrentLine(marker: Any)

    fun addColumnToLeftOfAllCurrentLines(
        alignment: TextAlignment,
        computeContent: (line: Line) -> TextSpan,
    )

    fun createViewAppendingToBlankLine(): MonospaceCanvas

    interface Line {
        val markers: Set<Any>
        fun mark(marker: Any)
    }

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
    }
}
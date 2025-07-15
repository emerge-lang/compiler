package compiler.diagnostic.rendering

import com.github.ajalt.mordant.rendering.TextStyle

/**
 * A piece of text with no linebreaks
 */
class TextSpan(val content: String, val style: TextStyle = DEFAULT_STYLE) {
    init {
        check(content.none { it == '\n' })
    }

    fun substring(from: Int, toExclusive: Int): TextSpan {
        return TextSpan(content.substring(from, toExclusive), style)
    }

    companion object {
        /**
         * Mordant defines this itself, but goes to great lengths to keep it to internal visibility.... wtf
         */
        val DEFAULT_STYLE = TextStyle(
            color = null,
            bgColor = null,
            bold = false,
            italic = false,
            underline = false,
            dim = false,
            inverse = false,
            strikethrough = false,
            hyperlink = null,
        )

        val EMPTY = TextSpan("", DEFAULT_STYLE)

        private val whitespaceCache = (0..20).associateWith {
            TextSpan(" ".repeat(it), DEFAULT_STYLE)
        }
        fun whitespace(width: Int): TextSpan = whitespaceCache[width] ?: TextSpan(" ".repeat(width), DEFAULT_STYLE)
    }
}
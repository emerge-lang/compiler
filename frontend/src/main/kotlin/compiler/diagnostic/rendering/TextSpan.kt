package compiler.diagnostic.rendering

/**
 * A piece of text with no linebreaks
 */
class TextSpan(val content: String) {
    init {
        check(content.none { it == '\n' })
    }

    operator fun plus(other: TextSpan): TextSpan {
        return TextSpan(content + other.content)
    }

    fun substring(from: Int, toExclusive: Int): TextSpan {
        return TextSpan(content.substring(from, toExclusive))
    }

    companion object {
        val EMPTY = TextSpan("")
    }
}
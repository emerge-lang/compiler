package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.isWhitespace

/**
 * Skips whitespace in the input stream
 */
class WhitespaceEaterRule() : Rule<Nothing> {
    override val descriptionOfAMatchingThing = "whitespace"

    override fun tryMatch(input: TokenSequence): MatchingResult<Nothing> {
        while (input.hasNext()) {
            input.mark()
            val token = input.next()!!
            if (!isWhitespace(token)) {
                input.rollback()
                break
            }

            input.commit()
        }

        return object : MatchingResult<Nothing>(
            ResultCertainty.OPTIMISTIC,
            null,
            emptySet()
        ) {
            override val isError = false
            override val isSuccess = true
        }
    }

    companion object {
        val instance: WhitespaceEaterRule = WhitespaceEaterRule()
    }
}
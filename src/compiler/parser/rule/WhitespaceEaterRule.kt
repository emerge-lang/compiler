package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.isWhitespace

/**
 * Skips whitespace in the input stream
 */
class WhitespaceEaterRule : Rule<Unit> {
    override val descriptionOfAMatchingThing = "whitespace"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<Unit> {
        while (input.hasNext()) {
            input.mark()
            val token = input.next()!!
            if (!isWhitespace(token)) {
                input.rollback()
                break
            }

            input.commit()
        }

        return RuleMatchingResultImpl(
            ResultCertainty.MATCHED,
            Unit,
            emptySet()
        )
    }

    companion object {
        val INSTANCE: WhitespaceEaterRule = WhitespaceEaterRule()
    }
}
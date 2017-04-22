package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.TokenSequence
import textutils.indentByFromSecondLine

/**
 * Matches the first of any given sub-rule
 */
open class EitherOfRule(
        open val subRules: Collection<Rule<*>>
) : Rule<Any?>
{
    override val descriptionOfAMatchingThing: String
        get() {
            val buf = StringBuilder()
            buf.append("one of:\n")
            for (rule in subRules) {
                buf.append("- ")
                buf.append(rule.descriptionOfAMatchingThing.indentByFromSecondLine(2))
            }

            return buf.toString()
        }

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<Any?> {
        for (rule in subRules) {
            input.mark()
            val result = rule.tryMatch(input)

            if (result.certainty >= ResultCertainty.MATCHED) {
                input.commit()
                return result
            }
            else {
                input.rollback()
            }
        }

        return RuleMatchingResultImpl(
            ResultCertainty.NOT_RECOGNIZED,
            null,
            setOf(Reporting.error(
                    "Unexpected ${input.peek()?.toStringWithoutLocation() ?: "end of input"}. Expected $descriptionOfAMatchingThing",
                    input.currentSourceLocation
            ))
        )
    }
}

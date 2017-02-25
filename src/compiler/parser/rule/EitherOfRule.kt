package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import textutils.indentByFromSecondLine
import compiler.parser.TokenSequence

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

    override fun tryMatch(input: TokenSequence): MatchingResult<Any?> {
        for (rule in subRules) {
            input.mark()
            val result = rule.tryMatch(input)

            if (result.isError) {
                input.rollback()
            }
            else {
                input.commit()
                return result
            }
        }

        return MatchingResult(
                ResultCertainty.DEFINITIVE,
                null,
                setOf(Reporting.error(
                        "Unexpected ${input.peek()!!.toStringWithoutLocation()}. Expected $descriptionOfAMatchingThing",
                        input.currentSourceLocation
                ))
        )
    }
}

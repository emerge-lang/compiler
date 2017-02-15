package parser.rule

import matching.ResultCertainty
import parser.Reporting
import parser.ReportingType
import textutils.indentByFromSecondLine
import parser.TokenSequence

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
            buf.append("One of:\n")
            for (rule in subRules) {
                buf.append("- ")
                buf.append(rule.descriptionOfAMatchingThing.indentByFromSecondLine(2))
                buf.append("\n")
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
                        ReportingType.MISSING_TOKEN,
                        "Expected $descriptionOfAMatchingThing but failed to match",
                        input.currentSourceLocation
                ))
        )
    }
}

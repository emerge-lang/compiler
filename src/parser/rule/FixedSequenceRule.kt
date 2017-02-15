package parser.rule

import textutils.indentByFromSecondLine
import matching.ResultCertainty
import parser.TokenSequence

open class FixedSequenceRule(
        private val subRules: List<Rule<*>>,
        /**
         * Keeps track of the indexes at which a level of correctnes can be assumed. E.g. when matching a rule with a
         * keyword exclusive to that rule: when that keyword appears in the lexer token stream it can be assumed that
         * the said rule is the correct one. As a result, that index is assigned the DEFINITVE certainty. No other
         * rules will then be matched against the same sequence of lexer tokens.
         */
        private var certaintySteps: List<Pair<Int, ResultCertainty>>
) : Rule<List<MatchingResult<*>>>
{
    init {
        if (certaintySteps.isEmpty()) {
            certaintySteps = listOf(0 to ResultCertainty.OPTIMISTIC)
        }
    }

    /** This should REALLY be overridden using describeAs() **/
    override val descriptionOfAMatchingThing: String
        get() {
            val buf = StringBuilder()
            buf.append("Tokens matching these rules in sequence:\n")
            for (rule in subRules) {
                buf.append("- ")
                buf.append(rule.descriptionOfAMatchingThing.indentByFromSecondLine(2))
                buf.append("\n")
            }

            return buf.toString()
        }

    override fun tryMatch(input: TokenSequence): MatchingResult<List<MatchingResult<*>>>
    {
        throw UnsupportedOperationException() // TODO: implement
    }
}
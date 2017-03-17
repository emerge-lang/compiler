package compiler.parser.rule

import textutils.indentByFromSecondLine
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence

open class FixedSequenceRule(
        private val subRules: List<Rule<*>>,
        /**
         * Keeps track of the indexes at which a level of correctnes can be assumed. E.g. when compiler.matching a rule with a
         * keyword exclusive to that rule: when that keyword appears in the compiler.lexer token stream it can be assumed that
         * the said rule is the correct one. As a result, that index is assigned the DEFINITVE certainty. No other
         * rules will then be matched against the same sequence of compiler.lexer tokens.
         */
        private var certaintySteps: List<Pair<Int, ResultCertainty>>
) : Rule<List<RuleMatchingResult<*>>>
{
    init {
        if (certaintySteps.isEmpty()) {
            certaintySteps = listOf(0 to ResultCertainty.NOT_RECOGNIZED)
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

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<*>>>
    {
        val results: MutableList<RuleMatchingResult<Any?>> = mutableListOf()
        var certainty: ResultCertainty = ResultCertainty.NOT_RECOGNIZED

        input.mark()

        subRules.forEachIndexed { index, rule ->
            val result = rule.tryMatch(input)
            if (result.item == null) {
                input.rollback()

                return@tryMatch RuleMatchingResultImpl(
                    certainty,
                    null,
                    results.flatMap { it.reportings } + result.reportings
                )
            }

            results.add(result)

            // determine new certainty
            val newCertainty = certaintySteps.find { it.first == index }?.second
            if (newCertainty != null) {
                certainty = newCertainty
            }
        }

        input.commit()

        return RuleMatchingResultImpl(
            certainty,
            results,
            emptySet()
        )
    }
}
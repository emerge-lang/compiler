package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class SequenceRule(
    private val subRules: List<Rule<*>>,
    private val givenName: String? = null,
) : Rule<List<RuleMatchingResult<*>>> {
    override val descriptionOfAMatchingThing: String by lazy {
        givenName?.let { return@lazy it }

        val buffer = StringBuilder(50)
        buffer.append("Tokens matching these rules in sequence:\n")
        subRules.forEach {
            buffer.append("- ")
            buffer.append(
                it.descriptionOfAMatchingThing
                    .indentByFromSecondLine(2)
                    .assureEndsWith('\n')
            )
        }
        buffer.toString()
    }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<*>>> {
        input.mark()

        val results = mutableListOf<RuleMatchingResult<*>>()
        val reportings = mutableListOf<Reporting>()
        var isAmbiguous = true

        subRules.forEachIndexed { ruleIndex, rule ->
            val result = rule.tryMatch(context, input)
            if (result.item == null && result.hasErrors) {
                input.rollback()

                return RuleMatchingResult(
                    isAmbiguous,
                    null,
                    result.reportings,
                )
            }

            results.add(result)
            reportings.addAll(result.reportings)
        }

        input.commit()

        return RuleMatchingResult(
            false, // ambiguity is only used to improve error messages; this is a successful match -> all good
            results,
            reportings
        )
    }
}
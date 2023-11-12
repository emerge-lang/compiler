package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class EitherOfRule(
    val options: List<Rule<*>>,
    val givenName: String? = null,
) : Rule<Any?> {
    override val descriptionOfAMatchingThing: String by lazy {
        givenName?.let { return@lazy it }
        val buffer = StringBuffer("one of:\n")
        options.forEach {
            buffer.append("- ")
            buffer.append(
                it.descriptionOfAMatchingThing
                    .indentByFromSecondLine(2)
                    .assureEndsWith('\n')
            )
        }

        buffer.toString()
    }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Any?> {
        input.mark()

        for (rule in options) {
            val result = rule.tryMatch(context, input)
            if (!result.isAmbiguous || !result.hasErrors) {
                input.commit()
                return result
            }
        }

        input.rollback()
        return RuleMatchingResult(
            true,
            null,
            setOf(
                Reporting.parsingError(
                    "Unexpected ${input.peek()?.toStringWithoutLocation() ?: "end of input"}, expected $descriptionOfAMatchingThing",
                    input.currentSourceLocation
                )
            )
        )
    }
}
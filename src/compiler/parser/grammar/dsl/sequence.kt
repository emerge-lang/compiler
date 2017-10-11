package compiler.parser.grammar.dsl

import compiler.lexer.TokenType
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import textutils.indentByFromSecondLine

internal fun tryMatchSequence(matcherFn: SequenceGrammar, input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<*>>> {
    input.mark()

    val results = mutableListOf<RuleMatchingResult<*>>()
    val reportings = mutableListOf<Reporting>()
    var certainty = ResultCertainty.NOT_RECOGNIZED
    var hasCertaintyBeenSet = false

    try {
        (object : BaseMatchingGrammarReceiver(input), SequenceRuleDefinitionReceiver {
            override fun handleResult(result: RuleMatchingResult<*>) {
                if (result.certainty < ResultCertainty.MATCHED) {
                    throw MatchingAbortedException(result.reportings)
                }
                results.add(result)
                reportings.addAll(result.reportings)
            }

            override var certainty: ResultCertainty
                get() = certainty
                set(value) {
                    certainty = value
                    hasCertaintyBeenSet = true
                }
        })
            .matcherFn()

        input.commit()

        return RuleMatchingResultImpl(
            if (hasCertaintyBeenSet) certainty else ResultCertainty.MATCHED,
            results,
            reportings
        )
    }
    catch (ex: MatchingAbortedException) {
        input.rollback()

        return RuleMatchingResultImpl(
            certainty,
            null,
            ex.reportings
        )
    }
}

internal fun describeSequenceGrammar(matcherFn: SequenceGrammar): String {
    val receiver = DescribingSequenceGrammarReceiver()
    receiver.matcherFn()
    return receiver.collectedDescription
}

interface SequenceRuleDefinitionReceiver : GrammarReceiver {
    var certainty: ResultCertainty
}

private class DescribingSequenceGrammarReceiver : SequenceRuleDefinitionReceiver, BaseDescribingGrammarReceiver() {
    override var certainty = ResultCertainty.NOT_RECOGNIZED

    private val buffer = StringBuilder(50)

    init {
        buffer.append("Tokens matching these rules in sequence:\n")
    }

    override fun handleItem(descriptionOfItem: String) {
        buffer.append("- ")
        buffer.append(descriptionOfItem.indentByFromSecondLine(2))
        buffer.append("\n")
    }

    val collectedDescription: String
        get() = buffer.toString()

    override fun tokenOfType(type: TokenType) {
        handleItem(type.name)
    }
}
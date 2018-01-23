package compiler.parser.grammar.dsl

import compiler.InternalCompilerError
import compiler.lexer.TokenType
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.reportings.Reporting
import textutils.indentByFromSecondLine

internal fun tryMatchEitherOf(matcherFn: Grammar, input: TokenSequence, mismatchCertainty: ResultCertainty): RuleMatchingResult<*> {
    input.mark()

    try {
        (object : BaseMatchingGrammarReceiver(input) {
            override fun handleResult(result: RuleMatchingResult<*>) {
                if (result.certainty >= ResultCertainty.MATCHED) {
                    throw SuccessfulMatchException(result)
                }
            }
        }).matcherFn()

        input.rollback()
        return RuleMatchingResultImpl(
            mismatchCertainty,
            null,
            setOf(Reporting.error(
                "Unexpected ${input.peek()?.toStringWithoutLocation() ?: "end of input"}, expected ${describeEitherOfGrammar(matcherFn)}",
                input.currentSourceLocation
            ))
        )
    }
    catch (ex: SuccessfulMatchException) {
        if (ex.result.item == null) {
            input.rollback()
            // TODO: FALLBACK!
        }
        else {
            input.commit()
        }

        return ex.result
    }
    catch (ex: MatchingAbortedException) {
        throw InternalCompilerError("How the heck did that happen?", ex)
    }
}

internal fun describeEitherOfGrammar(grammar: Grammar): String {
    val receiver = DescribingEitherOfGrammarReceiver()
    receiver.grammar()
    return receiver.collectedDescription
}

private class DescribingEitherOfGrammarReceiver : BaseDescribingGrammarReceiver() {
    private val buffer = StringBuilder(50)

    init {
        buffer.append("one of:\n")
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

private class SuccessfulMatchException(result: RuleMatchingResult<*>) : MatchingAbortedException(result, "A rule was sucessfully matched; Throwing this exception because other rules dont need to be attempted.")
/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.parser.grammar.dsl

import compiler.InternalCompilerError
import compiler.lexer.TokenType
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

internal fun tryMatchEitherOf(matcherFn: Grammar, input: TokenSequence, mismatchCertainty: ResultCertainty): RuleMatchingResult<*> {
    input.mark()

    try {
        (object : BaseMatchingGrammarReceiver(input) {
            override fun handleResult(result: RuleMatchingResult<*>) {
                mismatchCertainty
                if (result.certainty >= ResultCertainty.MATCHED) {
                    throw SuccessfulMatchException(result)
                }
            }
        }).matcherFn()

        input.rollback()
        return RuleMatchingResultImpl(
            mismatchCertainty,
            null,
            setOf(
                Reporting.parsingError(
                    "Unexpected ${input.peek()?.toStringWithoutLocation() ?: "end of input"}, expected ${describeEitherOfGrammar(matcherFn)}",
                    input.currentSourceLocation
                )
            )
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
        buffer.append(descriptionOfItem.indentByFromSecondLine(2).assureEndsWith('\n'))
    }

    val collectedDescription: String
        get() = buffer.toString()

    override fun tokenOfType(type: TokenType) {
        handleItem(type.name)
    }
}

private class SuccessfulMatchException(result: RuleMatchingResult<*>) : MatchingAbortedException(result, "A rule was sucessfully matched; Throwing this exception because other rules dont need to be attempted.")
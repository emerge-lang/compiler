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

import compiler.lexer.TokenType
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.parser.rule.hasErrors
import compiler.reportings.Reporting
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
                if (result.item == null || result.hasErrors) {
                    throw MatchingAbortedException(result)
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
            ex.result.reportings
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
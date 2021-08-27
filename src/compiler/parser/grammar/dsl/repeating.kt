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

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.parser.rule.hasErrors
import compiler.reportings.Reporting

internal fun <T> tryMatchRepeating(rule: Rule<T>, amount: IntRange, input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<T>>> {
    input.mark()

    var results = ArrayList<RuleMatchingResult<T>>(amount.first)
    var lastResult: RuleMatchingResult<T>? = null

    while (results.size < amount.last) {
        input.mark()

        lastResult = rule.tryMatch(input)
        if (lastResult.item == null) {
            input.rollback()
            // TODO: Fallback!

            if (lastResult.hasErrors && lastResult.certainty >= ResultCertainty.MATCHED) {
                return RuleMatchingResultImpl(
                    results.map { it.certainty }.maxOrNull() ?: ResultCertainty.MATCHED,
                    null,
                    lastResult.reportings
                )
            }

            break
        }

        input.commit()
        results.add(lastResult)
    }

    if (results.size >= amount.first) {
        input.commit()

        return RuleMatchingResultImpl(
            results.map { it.certainty }.minOrNull() ?: ResultCertainty.MATCHED,
            results,
            setOf()
        )
    }
    else
    {
        input.rollback()

        var errors = if (lastResult?.reportings != null && lastResult.reportings.isNotEmpty()) {
            lastResult.reportings
        }
        else {
            setOf(Reporting.parsingError(
                "Expected at least ${amount.first.wordifyEN} ${rule.descriptionOfAMatchingThing} but found only ${results.size.wordifyEN}",
                input.currentSourceLocation
            ))
        }

        return RuleMatchingResultImpl(
            ResultCertainty.NOT_RECOGNIZED,
            null,
            errors
        )
    }
}

internal fun describeRepeatingGrammar(grammar: SequenceGrammar, amount: IntRange): String {
    return "The following between ${amount.first.wordifyEN} and ${amount.last.wordifyEN} times:\n" +
        describeSequenceGrammar(grammar).prependIndent("  ")
}

private val Int.wordifyEN: String
    get() {
        if (this in 0..12) {
            return listOf(
                "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"
            )[this]
        }
        else
        {
            return this.toString()
        }
    }

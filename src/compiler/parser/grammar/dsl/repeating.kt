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
                    results.map { it.certainty }.max() ?: ResultCertainty.MATCHED,
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
            results.map { it.certainty }.min() ?: ResultCertainty.MATCHED,
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
            setOf(Reporting.error(
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
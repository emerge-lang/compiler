package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting

class RepeatingRule<T>(val rule: Rule<T>, val amount: IntRange) : Rule<List<T>> {
    override val descriptionOfAMatchingThing: String by lazy {
        "The following between ${amount.first.wordifyEN} and ${amount.last.wordifyEN} times:\n" +
                rule.descriptionOfAMatchingThing.prependIndent("  ")
    }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<List<T>> {
        input.mark()

        val results = ArrayList<RuleMatchingResult<T>>(amount.first)
        var lastResult: RuleMatchingResult<T>? = null

        while (results.size < amount.last) {
            input.mark()

            lastResult = rule.tryMatch(context, input)
            if (lastResult.item == null) {
                input.rollback()
                // TODO: Fallback!

                if (lastResult.hasErrors && !lastResult.isAmbiguous) {
                    return RuleMatchingResult(
                        results.all { it.isAmbiguous },
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

            return RuleMatchingResult(
                results.any { it.isAmbiguous },
                results.mapNotNull { it.item },
                results.flatMap { it.reportings },
            )
        }
        else
        {
            input.rollback()

            val errors = if (lastResult?.reportings != null && lastResult.reportings.isNotEmpty()) {
                lastResult.reportings
            }
            else {
                setOf(
                    Reporting.parsingError(
                    "Expected at least ${amount.first.wordifyEN} ${rule.descriptionOfAMatchingThing} but found only ${results.size.wordifyEN}",
                    input.currentSourceLocation
                ))
            }

            return RuleMatchingResult(
                true,
                null,
                errors
            )
        }
    }
}

private val Int.wordifyEN: String
    get()  = when(this) {
        in 0..12 -> listOf(
            "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"
        )[this]
        Int.MAX_VALUE -> "infinite"
        else -> this.toString()
    }
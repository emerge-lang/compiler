package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting

/**
 * Models the rule [rule] repeated 0..* or 1..* times (depending on [requireAtLeastOnce])
 */
class RepeatingRule<T>(
    private val rule: Rule<T>,
    private val requireAtLeastOnce: Boolean,
    private val maxRepeats: Int = Int.MAX_VALUE,
) : Rule<List<T>> {
    init {
        check(maxRepeats >= 1)
        check(!(maxRepeats == 1 && requireAtLeastOnce)) {
            "Rule ${rule.descriptionOfAMatchingThing} is required to match exactly once, use it directly."
        }
    }

    override val descriptionOfAMatchingThing: String by lazy {
        val buffer = StringBuilder()
        buffer.append("The following")
        if (requireAtLeastOnce) {
            buffer.append(" at least once and then")
        }
        buffer.append(" repeatedly")
        if (maxRepeats < Int.MAX_VALUE) {
            buffer.append(" at most ${maxRepeats.wordifyEN} times")
        }
        buffer.append(":\n")
        buffer.append(rule.descriptionOfAMatchingThing.prependIndent("  "))

        buffer.toString()
    }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<List<T>> {
        input.mark()

        val results = ArrayList<RuleMatchingResult<T>>(1)
        var lastResult: RuleMatchingResult<T>? = null

        while (results.size < maxRepeats && input.hasNext()) {
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

        if (!requireAtLeastOnce || results.isNotEmpty()) {
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
                    "Expected at least one ${rule.descriptionOfAMatchingThing} but found none",
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

    override val minimalMatchingSequence = if (requireAtLeastOnce) {
        rule.minimalMatchingSequence
    } else {
        sequenceOf(emptySequence())
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
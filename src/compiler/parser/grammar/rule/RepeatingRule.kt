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

    override val explicitName = null

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

    override fun match(context: Any, input: TokenSequence): RuleMatchingResult<List<T>> {
        input.mark()

        val results = ArrayList<RuleMatchingResult<T>>(1)
        var lastResult: RuleMatchingResult<T>? = null

        while (results.size < maxRepeats && input.hasNext()) {
            input.mark()

            lastResult = rule.match(context, input)
            if (lastResult.item == null) {
                input.rollback()
                // TODO: Fallback!

                if (lastResult.hasErrors && !lastResult.isAmbiguous) {
                    return RuleMatchingResult(
                        isAmbiguous = results.all { it.isAmbiguous },
                        marksEndOfAmbiguity = results.any { it.marksEndOfAmbiguity },
                        item = null,
                        reportings = lastResult.reportings
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
                isAmbiguous = results.any { it.isAmbiguous },
                marksEndOfAmbiguity = results.any { it.marksEndOfAmbiguity },
                results.mapNotNull { it.item },
                results.flatMap { it.reportings },
            )
        }

        input.rollback()

        val errors = if (lastResult?.reportings != null && lastResult.reportings.isNotEmpty()) {
            lastResult.reportings
        }
        else {
            setOf(
                Reporting.mismatch(
                    "at least one ${rule.descriptionOfAMatchingThing}",
                    "none",
                    input.currentSourceLocation,
                )
            )
        }

        return RuleMatchingResult(
            isAmbiguous = lastResult?.isAmbiguous ?: true,
            marksEndOfAmbiguity = lastResult?.marksEndOfAmbiguity ?: false,
            item = null,
            reportings = errors,
        )
    }

    override fun markAmbiguityResolved(inContext: Any) {
        rule.markAmbiguityResolved(inContext)
    }

    override val minimalMatchingSequence = if (requireAtLeastOnce) {
        rule.minimalMatchingSequence
    } else {
        sequence {
            yield(sequenceOf())
            yieldAll(rule.minimalMatchingSequence)
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
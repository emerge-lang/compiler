package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class SequenceRule(
    private val subRules: List<Rule<*>>,
    override val explicitName: String? = null,
) : Rule<List<MatchingResult<*>>> {
    override val descriptionOfAMatchingThing: String by lazy {
        explicitName?.let { return@lazy it }

        val buffer = StringBuilder(50 + subRules.size * 10)
        buffer.append("Tokens matching these rules in sequence:\n")
        subRules.forEach {
            buffer.append("- ")
            buffer.append(
                it.descriptionOfAMatchingThing
                    .indentByFromSecondLine(2)
                    .assureEndsWith('\n')
            )
        }
        buffer.toString()
    }

    override fun toString(): String = descriptionOfAMatchingThing

    override fun match(context: MatchingContext, input: TokenSequence): MatchingResult<List<MatchingResult<*>>> {
        input.mark()

        val results = mutableListOf<MatchingResult<*>>()
        val reportings = mutableListOf<Reporting>()
        var ambiguityResolved = false

        subRules.forEachIndexed { ruleIndex, rule ->
            val result = rule.match(SequenceIndexContext(context, this, ruleIndex), input)
            if (result.item == null && result.hasErrors) {
                input.rollback()

                return MatchingResult(
                    isAmbiguous = !ambiguityResolved && result.isAmbiguous,
                    false,
                    null,
                    result.reportings,
                )
            }

            if (result.marksEndOfAmbiguity) {
                ambiguityResolved = true
            }
            results.add(result)
            reportings.addAll(result.reportings)
        }

        input.commit()

        return MatchingResult(
            isAmbiguous = false,
            marksEndOfAmbiguity = ambiguityResolved,
            item = results,
            reportings = reportings,
        )
    }

    override fun markAmbiguityResolved(inContext: MatchingContext) {
        this.subRules.forEachIndexed { ruleIndex, rule ->
            rule.markAmbiguityResolved(SequenceIndexContext(inContext, this, ruleIndex))
        }
    }

    // the logical thing might be to do a cross-product of all the sub-rule options. But actually tracking that
    // context during matching is a MAJOR hassle. As a simplification we put a limitation on the power of the ambiguity
    // resolution: it will only consider the first diversion
    override val minimalMatchingSequence: Sequence<Sequence<ExpectedToken>> = run minimalSequence@{
        val sequencesBeforeDiversion = ArrayList<Sequence<ExpectedToken>>(subRules.size / 2)
        var diversion: Sequence<Sequence<ExpectedToken>> = sequenceOf(emptySequence())
        var diversionSeen = false
        val sequencesAfterDiversion = ArrayList<Sequence<ExpectedToken>>(subRules.size / 2)

        for (rule in subRules) {
            val unambiguousSequence = rule.minimalMatchingSequence.singleOrNull()
            if (unambiguousSequence == null) {
                if (diversionSeen) {
                    // this is the second diversion => limit reached
                    break
                }
                diversionSeen = true
                diversion = rule.minimalMatchingSequence
                continue
            }
            else if (diversionSeen) {
                sequencesAfterDiversion.add(unambiguousSequence)
            }
            else {
                sequencesBeforeDiversion.add(unambiguousSequence)
            }
        }

        val prefix: Sequence<ExpectedToken> = sequencesBeforeDiversion.asSequence().flatMapIndexed { ruleIndex, prefixSequence ->
            prefixSequence.map { prefixToken ->
                SequenceDelegatingExpectedToken(prefixToken, ruleIndex, this)
            }
        }

        if (!diversionSeen) {
            return@minimalSequence sequenceOf(prefix)
        }

        val suffix: Sequence<ExpectedToken> = sequencesAfterDiversion.asSequence().flatMapIndexed { ruleIndexAfterDiversion, suffixSequence ->
            suffixSequence.map { suffixToken ->
                SequenceDelegatingExpectedToken(suffixToken, sequencesBeforeDiversion.size + 1 + ruleIndexAfterDiversion, this)
            }
        }

        return@minimalSequence diversion.map {
            prefix + it.map { diversionToken ->
                SequenceDelegatingExpectedToken(diversionToken, sequencesBeforeDiversion.size, this)
            } + suffix
        }
    }

    private class SequenceDelegatingExpectedToken(
        val delegate: ExpectedToken,
        val indexOfRuleObtainedFrom: Int,
        val parentSequence: SequenceRule,
    ) : ExpectedToken {
        override fun markAsRemovingAmbiguity(inContext: MatchingContext) {
            delegate.markAsRemovingAmbiguity(SequenceIndexContext(inContext, parentSequence, indexOfRuleObtainedFrom))
        }

        override fun unwrap() = delegate.unwrap()
        override fun toString() = delegate.toString()
        override fun isCloneOf(other: ExpectedToken): Boolean {
            return other is SequenceDelegatingExpectedToken &&
                    this.indexOfRuleObtainedFrom == other.indexOfRuleObtainedFrom &&
                    this.parentSequence == other.parentSequence &&
                    this.delegate.isCloneOf(other.delegate)
        }
    }
}

private data class SequenceIndexContext(
    private val parentContext: Any,
    private val sequenceRule: SequenceRule,
    private val sequenceIndex: Int,
) : MatchingContext() {
    override fun toString(): String = "sequence" + (sequenceRule.explicitName?.let { "<$it>" } ?: "") + "#$sequenceIndex"
}
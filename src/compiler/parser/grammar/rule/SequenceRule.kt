package compiler.parser.grammar.rule

import compiler.hasFewerElementsThan
import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class SequenceRule(
    private val subRules: List<Rule<*>>,
    override val explicitName: String? = null,
) : Rule<List<RuleMatchingResult<*>>> {
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

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<*>>> {
        input.mark()

        val results = mutableListOf<RuleMatchingResult<*>>()
        val reportings = mutableListOf<Reporting>()
        var ambiguityResolved = false

        subRules.forEachIndexed { ruleIndex, rule ->
            val result = rule.tryMatch(SequenceIndexContext(context, this, ruleIndex), input)
            if (result.item == null && result.hasErrors) {
                input.rollback()

                return RuleMatchingResult(
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

        return RuleMatchingResult(
            isAmbiguous = false,
            marksEndOfAmbiguity = ambiguityResolved,
            item = results,
            reportings = reportings,
        )
    }

    private val firstDiversionAtRuleIndex = subRules.asSequence()
        .takeWhile { it.minimalMatchingSequence.hasFewerElementsThan(2) }
        .count()

    // the logical thing might be to do a cross-product of all the sub-rule options. But actually tracking that
    // context during matching is a MAJOR hassle. As a simplification we put a limitation on the set of possible
    // grammars: sequences can reference unambiguous (= single option) sub-rules and must become unambiguous
    // at their first diversion into options at the latest
    // this COULD be extended to limiting sequences to one diversion before they become unambiguous, but allowing
    // more unambiguous sub-rules after the diversion.
    override val minimalMatchingSequence: Sequence<Sequence<ExpectedToken>> = run minimalSequnce@{
        val prefix = subRules
            .subList(0, firstDiversionAtRuleIndex)
            .asSequence()
            .map { it.minimalMatchingSequence.single() }
            .flatMapIndexed { ruleIndex, ruleMinimalSequence -> ruleMinimalSequence.map { prefixExpectedToken ->
                SequenceDelegatingExpectedToken(prefixExpectedToken, ruleIndex, this)
            } }

        val diversion: Sequence<Sequence<ExpectedToken>> = if (subRules.isEmpty() || firstDiversionAtRuleIndex !in subRules.indices) {
            sequenceOf(emptySequence())
        } else {
            subRules[firstDiversionAtRuleIndex].minimalMatchingSequence
        }

        diversion.map { prefix + it.map { diversionOptionToken ->
            SequenceDelegatingExpectedToken(diversionOptionToken, firstDiversionAtRuleIndex, this)
        } }
    }

    private class SequenceDelegatingExpectedToken(
        val delegate: ExpectedToken,
        val indexOfRuleObtainedFrom: Int,
        val parentSequence: SequenceRule,
    ) : ExpectedToken {
        override fun markAsRemovingAmbiguity(inContext: Any) {
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
) {
    override fun toString(): String = "sequence" + (sequenceRule.explicitName?.let { "<$it>" } ?: "") + "#$sequenceIndex"
}
package compiler.parser.grammar.rule

import compiler.InternalCompilerError
import compiler.parser.TokenSequence
import compiler.parser.grammar.rule.MappingIterator.Companion.mapRemainingIndexed
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine
import java.util.IdentityHashMap

class SequenceRule(
    private val subRules: List<Rule<*>>,
    private val givenName: String? = null,
) : Rule<List<RuleMatchingResult<*>>> {
    override val descriptionOfAMatchingThing: String by lazy {
        givenName?.let { return@lazy it }

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

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<List<RuleMatchingResult<*>>> {
        input.mark()

        val results = mutableListOf<RuleMatchingResult<*>>()
        val reportings = mutableListOf<Reporting>()
        val unambiguousStartingAtIndex: Int = unambiguousStartingAtSubRuleIndexByContext[context] ?: 0
        check(unambiguousStartingAtIndex <= firstDiversionAtRuleIndex)
        var subRuleContext = context

        subRules.forEachIndexed { ruleIndex, rule ->
            if (ruleIndex > unambiguousStartingAtIndex) {
                subRuleContext = Unit
            }

            val result = rule.tryMatch(subRuleContext, input)
            if (result.item == null && result.hasErrors) {
                input.rollback()

                return RuleMatchingResult(
                    ruleIndex <= unambiguousStartingAtIndex,
                    null,
                    result.reportings,
                )
            }

            results.add(result)
            reportings.addAll(result.reportings)
        }

        input.commit()

        return RuleMatchingResult(
            false, // ambiguity is only used to improve error messages; this is a successful match -> all good
            results,
            reportings
        )
    }

    private val unambiguousStartingAtSubRuleIndexByContext = HashMap<Any, Int>()

    private val firstDiversionAtRuleIndex = subRules.asSequence()
        .takeWhile { it.minimalMatchingSequence.take(2).count() <= 1 }
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
                SequenceDelegatingExpectedToken(prefixExpectedToken, ruleIndex, this::storeAmbiguityResolution)
            } }

        val diversion: Sequence<Sequence<ExpectedToken>> = if (subRules.isEmpty() || firstDiversionAtRuleIndex !in subRules.indices) {
            sequenceOf(emptySequence())
        } else {
            subRules[firstDiversionAtRuleIndex].minimalMatchingSequence
        }

        diversion.map { prefix + it.map { diversionOptionToken ->
            SequenceDelegatingExpectedToken(diversionOptionToken, firstDiversionAtRuleIndex, this::storeAmbiguityResolution)
        } }
    }


    private fun storeAmbiguityResolution(ruleIndex: Int, inContext: Any) {
        if (unambiguousStartingAtSubRuleIndexByContext.putIfAbsent(inContext, ruleIndex) != null) {
            throw InternalCompilerError("Resolving ambiguity multiple times for context $inContext")
        }
    }
}

private data class SequenceIndexContext(
    private val parentContext: Any,
    private val sequenceIndex: Int,
)

private class SequenceDelegatingExpectedToken(
    val delegate: ExpectedToken,
    val indexOfRuleObtainedFrom: Int,
    val onAmbiguityResolved: (ruleIndex: Int, inContext: Any) -> Any?,
) : ExpectedToken {
    override fun markAsRemovingAmbiguity(inContext: Any) {
        delegate.markAsRemovingAmbiguity(SequenceIndexContext(inContext, indexOfRuleObtainedFrom))
        onAmbiguityResolved(indexOfRuleObtainedFrom, inContext)
    }

    override fun unwrap() = delegate.unwrap()
    override fun toString() = delegate.toString()
}
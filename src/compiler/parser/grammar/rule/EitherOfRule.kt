package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.pivot
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class EitherOfRule(
    val options: List<Rule<*>>,
    val givenName: String? = null,
) : Rule<Any?> {
    override val descriptionOfAMatchingThing: String by lazy {
        givenName?.let { return@lazy it }
        val buffer = StringBuffer("one of:\n")
        options.forEach {
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

    private val ambiguityResolvedForContexts = HashSet<Any>()

    override val minimalMatchingSequence: Sequence<Sequence<ExpectedToken>> = options.asSequence()
            .flatMapIndexed { optionIndex, optionRule ->
                optionRule.minimalMatchingSequence.mapIndexed { _, optionSequence ->
                    optionSequence.mapIndexed { _, expectedToken ->
                        EitherOfWrappedExpectedToken(expectedToken, this, optionIndex, this.ambiguityResolvedForContexts::add)
                    }
                }
            }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Any?> {
        if (context !in ambiguityResolvedForContexts && context == Unit) {
            resolveAmbiguityForContext(context)
        }

        input.mark()

        options.forEachIndexed { optionIndex, option ->
            val result = option.tryMatch(EitherOfOptionContext(context, this, optionIndex), input)
            if (!result.isAmbiguous || !result.hasErrors) {
                input.commit()
                return result
            }
        }

        input.rollback()
        return RuleMatchingResult(
            true,
            null,
            setOf(
                Reporting.parsingError(
                    "Unexpected ${input.peek()?.toStringWithoutLocation() ?: "end of input"}, expected $descriptionOfAMatchingThing",
                    input.currentSourceLocation
                )
            )
        )
    }

    private fun resolveAmbiguityForContext(context: Any) {
        minimalMatchingSequence.pivot().forEach { tokensAtIndexIntoThisRule ->
            tokensAtIndexIntoThisRule
                .filterNotNull()
                .groupUsing(ExpectedToken::matchesSameTokensAs)
                .mapNotNull { tokenGroup ->
                    // there could be the same token on multiple paths. Still, if its the exact same token
                    // present on multiple paths, it's unambiguous already
                    tokenGroup
                        .groupUsing { a, b -> a.unwrap() === b.unwrap() }
                        .singleOrNull()
                }
                .flatten()
                .forEach { it.markAsRemovingAmbiguity(context) }
        }
    }
}

private data class EitherOfOptionContext(
    private val parentContext: Any,
    private val parentRule: Rule<*>,
    private val optionIndex: Int,
)

private class EitherOfWrappedExpectedToken(
    val delegate: ExpectedToken,
    val eitherOfRule: Rule<*>,
    val optionIndex: Int,
    val onAmbiguityResolved: (context: Any) -> Any?,
) : ExpectedToken {
    override fun markAsRemovingAmbiguity(inContext: Any) {
        onAmbiguityResolved(inContext)
        delegate.markAsRemovingAmbiguity(EitherOfOptionContext(inContext, eitherOfRule, optionIndex))
    }

    override fun unwrap() = delegate.unwrap()

    override fun toString() = delegate.toString()
}

/**
 * @param equals an alternative [Any.equals] implementation, must adhere to the same contract.
 */
private fun <T> Iterable<T>.groupUsing(equals: (T, T) -> Boolean): List<List<T>> {
    val groups = mutableListOf<MutableList<T>>()
    element@for (element in this) {
        for (group in groups) {
            if (equals(group.first(), element)) {
                group.add(element)
                continue@element
            }
        }
        groups.add(mutableListOf(element))
    }

    return groups
}
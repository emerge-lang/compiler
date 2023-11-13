package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine
import java.util.NoSuchElementException

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

    private val ambiguityResolvedForContexts = HashSet<Any>()

    override val minimalMatchingSequence: Sequence<Sequence<ExpectedToken>> = options.asSequence()
            .flatMapIndexed { optionIndex, optionRule ->
                optionRule.minimalMatchingSequence.mapIndexed { _, subOptionSequence ->
                    subOptionSequence.mapIndexed { _, expectedToken ->
                        EitherOfWrappedExpectedToken(expectedToken, optionIndex, this.ambiguityResolvedForContexts::add)
                    }
                }
            }

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Any?> {
        if (context !in ambiguityResolvedForContexts) {
            check(context == Unit) { "Evaluating rule $descriptionOfAMatchingThing in context $context but ambiguity for this context is not resolved yet." }
            resolveAmbiguityForContext(context)
        }

        input.mark()

        options.forEachIndexed { optionIndex, option ->
            val result = option.tryMatch(EitherOfOptionContext(context, optionIndex), input)
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
                .mapNotNull { tokenGroup -> tokenGroup.singleOrNull() }
                .forEach { it.markAsRemovingAmbiguity(context) }
        }
    }
}

private data class EitherOfOptionContext(
    private val parentContext: Any,
    private val optionIndex: Int,
)

private class EitherOfWrappedExpectedToken(
    val delegate: ExpectedToken,
    val optionIndex: Int,
    val onAmbiguityResolved: (context: Any) -> Any?,
) : ExpectedToken {
    override fun markAsRemovingAmbiguity(inContext: Any) {
        onAmbiguityResolved(inContext)
        delegate.markAsRemovingAmbiguity(EitherOfOptionContext(inContext, optionIndex))
    }

    override fun unwrap() = delegate.unwrap()

    override fun toString() = delegate.toString()
}

/**
 * @return all the 0th, 1st, 2nd, ... elements of the sub-sequences in a list each
 */
private fun <T : Any> Sequence<Sequence<T>>.pivot(): Sequence<List<T?>> {
    val subSequenceIterators = this.mapIndexed { _, it -> it.iterator() }.toList()
    return object : Sequence<List<T?>> {
        override fun iterator(): Iterator<List<T?>> {
            return object : Iterator<List<T?>> {
                private var next: List<T?>? = null

                private fun tryFindNext() {
                    if (next != null) {
                        return
                    }

                    val nextLocal = subSequenceIterators.map { if (it.hasNext()) it.next() else null }
                    next = nextLocal.takeIf { it.any { e -> e != null }}
                }

                override fun hasNext(): Boolean {
                    tryFindNext()

                    return next != null
                }

                override fun next(): List<T?> {
                    tryFindNext()
                    return next ?: throw NoSuchElementException()
                }
            }
        }
    }
}

/**
 * @param equals an alternative [Any.equals] implementation, but must adhere to the same contract.
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
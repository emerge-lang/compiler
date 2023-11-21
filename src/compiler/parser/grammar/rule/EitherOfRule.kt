package compiler.parser.grammar.rule

import compiler.parser.TokenSequence
import compiler.pivot
import compiler.reportings.Reporting
import textutils.assureEndsWith
import textutils.indentByFromSecondLine

class EitherOfRule(
    private val options: List<Rule<*>>,
    override val explicitName: String? = null,
) : Rule<Any?> {
    override val descriptionOfAMatchingThing: String by lazy {
        explicitName?.let { return@lazy it }
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
        if (context !in ambiguityResolvedForContexts) {
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
        val reporting = input.peek()?.let {
            Reporting.mismatch(descriptionOfAMatchingThing, it)
        } ?: Reporting.unexpectedEOI(descriptionOfAMatchingThing, input.currentSourceLocation)

        return RuleMatchingResult(
            isAmbiguous = true,
            marksEndOfAmbiguity = false,
            item = null,
            reportings = setOf(reporting),
        )
    }

    private fun resolveAmbiguityForContext(context: Any) {
        minimalMatchingSequence.pivot().forEach { tokensAtIndexIntoThisRule ->
            tokensAtIndexIntoThisRule
                .filterNotNull()
                .groupUsing(ExpectedToken::couldMatchSameTokenAs)
                .filter { equalExpectedTokens -> equalExpectedTokens.isNotEmptyAndIsAllClones() }
                .flatten()
                .forEach { it.markAsRemovingAmbiguity(context) }
        }
        ambiguityResolvedForContexts.add(context)
    }
}

private data class EitherOfOptionContext(
    private val parentContext: Any,
    private val eitherOfRule: EitherOfRule,
    private val optionIndex: Int,
) {
    override fun toString() = "eitherOf" + (eitherOfRule.explicitName?.let { "<$it>" } ?: "") + "#$optionIndex"
}

private class EitherOfWrappedExpectedToken(
    val delegate: ExpectedToken,
    val eitherOfRule: EitherOfRule,
    val optionIndex: Int,
    val onAmbiguityResolved: (context: Any) -> Any?,
) : ExpectedToken {
    override fun markAsRemovingAmbiguity(inContext: Any) {
        onAmbiguityResolved(inContext)
        delegate.markAsRemovingAmbiguity(EitherOfOptionContext(inContext, eitherOfRule, optionIndex))
    }

    override fun unwrap() = delegate.unwrap()

    override fun toString() = delegate.toString()

    override fun isCloneOf(other: ExpectedToken): Boolean {
        return other is EitherOfWrappedExpectedToken &&
                this.optionIndex == other.optionIndex &&
                this.eitherOfRule == other.eitherOfRule &&
                this.delegate.isCloneOf(other.delegate)
    }
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

private fun Iterable<ExpectedToken>.isNotEmptyAndIsAllClones(): Boolean {
    val iterator = iterator()
    if (!iterator.hasNext()) {
        return false
    }

    val pivot = iterator.next()
    while (iterator.hasNext()) {
        val element = iterator.next()
        if (!element.isCloneOf(pivot)) {
            return false
        }
    }

    return true
}
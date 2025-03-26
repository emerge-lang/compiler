package compiler.parser.grammar.rule

import compiler.lexer.Token

class RepeatingRule<Item : Any>(
    val subRule: Rule<Item>,
    atLeastOnce: Boolean,
    val upperBound: UInt,
) : Rule<RepeatingRule.RepeatedMatch<Item>> {
    private val lowerBound: UInt = if (atLeastOnce) 1u else 0u
    init {
        check(lowerBound <= Int.MAX_VALUE.toUInt())
        check(upperBound >= lowerBound)
    }

    override val explicitName: String? get() {
        if (subRule.explicitName == null) {
            return null
        }
        val upperBoundStr = if (upperBound == UInt.MAX_VALUE) "*" else upperBound.toString()
        return "$lowerBound..$upperBoundStr ${subRule.explicitName}"
    }

    override fun toString() = explicitName ?: "Repeating($subRule)"

    override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<RepeatedMatch<Item>>> {
        return sequence {
            match(tokens, atIndex, emptyList())
        }
    }

    override fun <R : Any> visit(visitor: GrammarVisitor<R>) {
        visitNoReference(visitor)
    }

    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitRepeating(subRule, lowerBound, upperBound.takeUnless { it == UInt.MAX_VALUE })
    }

    private suspend fun SequenceScope<MatchingResult<RepeatedMatch<Item>>>.match(tokens: Array<Token>, atIndex: Int, resultsThusFar: List<MatchingResult.Success<Item>>) {
        for (subResult in subRule.match(tokens, atIndex)) {
            when (subResult) {
                is MatchingResult.Success<Item> -> {
                    if (resultsThusFar.size.toUInt() + 1u < upperBound) {
                        match(tokens, subResult.continueAtIndex, resultsThusFar + subResult)
                    } else {
                        yield(MatchingResult.Success(RepeatedMatch(resultsThusFar + subResult), subResult.continueAtIndex))
                    }
                }
                is MatchingResult.Error -> {
                    yield(subResult)
                    continue
                }
            }
        }

        if (resultsThusFar.size.toUInt() >= lowerBound) {
            yield(MatchingResult.Success(RepeatedMatch(resultsThusFar), resultsThusFar.lastOrNull()?.continueAtIndex ?: atIndex))
        }
    }

    class RepeatedMatch<Item : Any>(val matches: List<MatchingResult.Success<Item>>) {
        companion object {
            private val empty: RepeatedMatch<Any> = RepeatedMatch(emptyList())

            @Suppress("UNCHECKED_CAST")
            fun <T : Any> empty(): RepeatedMatch<T> = empty as RepeatedMatch<T>
        }
    }

    private suspend fun <Item : Any> SequenceScope<MatchingResult<RepeatedMatch<Item>>>.alternatives(results: List<MatchingResult.Success<Item>>, lowerBound: UInt, originalStartIndex: Int) {
        for (nResults in results.size downTo lowerBound.toInt()) {
            val subset = RepeatedMatch(results.subList(0, nResults))
            yield(MatchingResult.Success(subset, subset.matches.lastOrNull()?.continueAtIndex ?: originalStartIndex))
        }
    }
}
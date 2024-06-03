package compiler.parser.grammar.rule

import compiler.lexer.Token

class RepeatingRule<Item : Any>(
    val subRule: Rule<Item>,
    val atLeastOnce: Boolean,
    val upperBound: UInt,
) : Rule<RepeatingRule.RepeatedMatch<Item>> {
    override val explicitName: String? get() {
        if (subRule.explicitName == null) {
            return null
        }
        val lowerBoundStr = if (atLeastOnce) "1" else "0"
        val upperBoundStr = if (upperBound == UInt.MAX_VALUE) "*" else upperBound.toString()
        return "$lowerBoundStr..$upperBoundStr ${subRule.explicitName}"
    }

    override fun toString() = explicitName ?: "Repeating($subRule)"

    override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<RepeatedMatch<Item>>> {
        return sequence {
            if (!atLeastOnce) {
                yield(MatchingResult.Success(RepeatedMatch(emptyList()), atIndex))
            }
            yieldAll(match(tokens, atIndex, emptyList()))
        }
    }

    private fun match(tokens: Array<Token>, atIndex: Int, resultsThusFar: List<Item>): Sequence<MatchingResult<RepeatedMatch<Item>>> {
        return subRule.match(tokens, atIndex)
            .flatMap { subOption ->
                if (subOption is MatchingResult.Error) {
                    sequenceOf(subOption)
                } else {
                    subOption as MatchingResult.Success<Item>
                    val newResults = resultsThusFar + subOption.item
                    val thisResultSequence = sequenceOf(MatchingResult.Success(RepeatedMatch(newResults), subOption.continueAtIndex))
                    val furtherResults = if (newResults.size.toUInt() >= upperBound) emptySequence() else {
                        match(tokens, subOption.continueAtIndex, resultsThusFar + listOf(subOption.item))
                    }
                    thisResultSequence + furtherResults
                }
            }
    }

    class RepeatedMatch<Item : Any>(val matches: List<Item>) {
        companion object {
            private val empty: RepeatedMatch<Any> = RepeatedMatch(emptyList())

            @Suppress("UNCHECKED_CAST")
            fun <T : Any> empty(): RepeatedMatch<T> = empty as RepeatedMatch<T>
        }
    }
}
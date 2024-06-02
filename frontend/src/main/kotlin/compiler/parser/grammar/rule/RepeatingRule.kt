package compiler.parser.grammar.rule

class RepeatingRule<Item : Any>(
    val subRule: Rule<Item>,
    val upperBound: Int,
) : Rule<RepeatingRule.RepeatedMatch<Item>> {
    init {
        require(upperBound >= 0)
    }

    override val explicitName: String? get() {
        if (subRule.explicitName == null) {
            return null
        }
        val upperBoundStr = if (upperBound == Int.MAX_VALUE) "*" else upperBound.toString()
        return "0..$upperBoundStr ${subRule.explicitName}"
    }

    override fun toString() = explicitName ?: "Repeating($subRule)"

    override fun startMatching(continueWith: MatchingContinuation<RepeatedMatch<Item>>): OngoingMatch {
        return BranchingOngoingMatch(
            listOf(
                RepeaterRule(emptyList()),
                NoopRule(MatchingResult(RepeatedMatch.empty(), emptySet())),
            ),
            continueWith
        )
    }

    private inner class RepeaterRule(
        val resultsThusFar: List<MatchingResult<Item>>,
    ) : Rule<RepeatedMatch<Item>> {
        override val explicitName get() = this@RepeatingRule.explicitName

        override fun startMatching(continueWith: MatchingContinuation<RepeatedMatch<Item>>): OngoingMatch {
            return subRule.startMatching(object : MatchingContinuation<Item> {
                override fun resume(result: MatchingResult<Item>): OngoingMatch {
                    val partialResultList = resultsThusFar + result
                    val partialResult = MatchingResult(RepeatedMatch(partialResultList), partialResultList.flatMap { it.reportings })
                    if (result.hasErrors || partialResultList.size >= this@RepeatingRule.upperBound) {
                        return continueWith.resume(partialResult)
                    }

                    return BranchingOngoingMatch(
                        listOf(
                            RepeaterRule(partialResultList),
                            NoopRule(partialResult),
                        ),
                        continueWith
                    )
                }
            })
        }
    }

    class RepeatedMatch<Item : Any>(val matches: List<MatchingResult<Item>>) {
        companion object {
            private val empty: RepeatedMatch<Any> = RepeatedMatch(emptyList())

            @Suppress("UNCHECKED_CAST")
            fun <T : Any> empty(): RepeatedMatch<T> = empty as RepeatedMatch<T>
        }
    }
}
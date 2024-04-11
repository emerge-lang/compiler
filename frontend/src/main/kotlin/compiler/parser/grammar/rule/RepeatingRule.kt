package compiler.parser.grammar.rule

class RepeatingRule<Item : Any>(
    val subRule: Rule<Item>,
    val upperBound: Int,
) : Rule<RepeatingRule.RepeatedMatch<Item>> {
    init {
        require(upperBound >= 0)
    }

    override val explicitName: String get() {
        val upperBoundStr = if (upperBound == Int.MAX_VALUE) "*" else upperBound.toString()
        return "0..$upperBoundStr $subRule"
    }

    override fun toString() = explicitName

    override fun startMatching(continueWith: MatchingContinuation<RepeatedMatch<Item>>): OngoingMatch {
        return BranchingOngoingMatch(
            listOf(
                NoopRule(MatchingResult(RepeatedMatch.empty(), emptySet())),
                RepeaterRule(),
            ),
            continueWith
        )
    }

    private inner class RepeaterRule : Rule<RepeatedMatch<Item>> {
        val results = ArrayList<MatchingResult<Item>>()
        override val explicitName get() = this@RepeatingRule.explicitName

        override fun startMatching(continueWith: MatchingContinuation<RepeatedMatch<Item>>): OngoingMatch {
            return subRule.startMatching(object : MatchingContinuation<Item> {
                override fun resume(result: MatchingResult<Item>): OngoingMatch {
                    results.add(result)
                    val partialResult = MatchingResult(RepeatedMatch(results.subList(0, results.size)), results.flatMap { it.reportings })
                    if (result.hasErrors || results.size >= this@RepeatingRule.upperBound) {
                        return continueWith.resume(partialResult)
                    }

                    return BranchingOngoingMatch(
                        listOf(
                            NoopRule(partialResult),
                            this@RepeaterRule,
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
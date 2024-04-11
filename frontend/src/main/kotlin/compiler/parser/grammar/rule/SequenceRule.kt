package compiler.parser.grammar.rule

class SequenceRule(
    val subRules: Array<Rule<*>>,
    override val explicitName: String?,
) : Rule<SequenceRule.MatchedSequence> {
    init {
        require(subRules.isNotEmpty())
    }

    override fun startMatching(afterSequence: MatchingContinuation<MatchedSequence>): OngoingMatch {
        val results = ArrayList<MatchingResult<*>>(subRules.size)
        val selfSequenceContinuation = object : MatchingContinuation<Any> {
            override fun resume(result: MatchingResult<Any>): OngoingMatch {
                results.add(result)
                if (result.hasErrors) {
                    return afterSequence.resume(MatchingResult(null, results.flatMap { it.reportings }))
                }

                if (results.size >= subRules.size) {
                    val sequenceResult = MatchingResult(
                        MatchedSequence(results).takeUnless { results.any { it.hasErrors } },
                        results.flatMap { it.reportings },
                    )
                    return afterSequence.resume(sequenceResult)
                } else {
                    return subRules[results.size].startMatching(this)
                }
            }
        }

        return subRules.first().startMatching(selfSequenceContinuation)
    }

    override fun toString() = explicitName ?: super.toString()

    class MatchedSequence(val subResults: List<MatchingResult<*>>)
}
package compiler.parser.grammar.rule

class SequenceRule(
    val subRules: Array<Rule<*>>,
    override val explicitName: String?,
) : Rule<SequenceRule.MatchedSequence> {
    init {
        require(subRules.isNotEmpty())
    }

    override fun startMatching(continueWith: MatchingContinuation<MatchedSequence>): OngoingMatch {
        return subRules.first().startMatching(ContinuationImpl(emptyList(), 1, continueWith))
    }

    private inner class ContinuationImpl(
        val resultsThusFar: List<MatchingResult<*>>,
        val nextRuleIndex: Int,
        val afterSequence: MatchingContinuation<MatchedSequence>,
    ) : MatchingContinuation<Any> {
        override fun resume(result: MatchingResult<Any>): OngoingMatch {
            val nextResults = resultsThusFar + result
            if (result.hasErrors) {
                return afterSequence.resume(MatchingResult(null, nextResults.flatMap { it.reportings }))
            }

            if (nextRuleIndex == subRules.size) {
                return afterSequence.resume(MatchingResult(MatchedSequence(nextResults), nextResults.flatMap { it.reportings }))
            }

            return subRules[nextRuleIndex].startMatching(ContinuationImpl(nextResults, nextRuleIndex + 1, afterSequence))
        }
    }

    override fun toString() = explicitName ?: super.toString()

    data class MatchedSequence(val subResults: List<MatchingResult<*>>)
}
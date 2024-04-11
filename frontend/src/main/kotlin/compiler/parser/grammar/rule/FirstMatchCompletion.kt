package compiler.parser.grammar.rule

import compiler.reportings.ParsingMismatchReporting

/**
 * Only cares about the first [MatchingResult] with [MatchingResult.hasErrors] `== false`. If it doesn't
 * get hold of one, aggregates the [Reporting]s
 */
class FirstMatchCompletion<Item : Any> : MatchingContinuation<Item> {
    private var successResult: MatchingResult<Item>? = null
    private var carryReporting: ParsingMismatchReporting? = null

    val result: MatchingResult<Item> get() {
        successResult?.let { return it }
        val error = carryReporting ?: error("Did not receive a single result - neither error nor success")
        return MatchingResult(null, setOf(error))
    }

    override fun resume(result: MatchingResult<Item>): OngoingMatch {
        if (successResult != null) {
            // ignore
            return OngoingMatch.Completed
        }

        if (!result.hasErrors) {
            successResult = result
            return OngoingMatch.Completed
        }

        if (result.hasErrors) {
            if (carryReporting == null) {
                carryReporting = result.reportings.reduce(::reduceCombineParseError)
            } else {
                carryReporting = result.reportings.fold(carryReporting!!, ::reduceCombineParseError)
            }
        }
        return OngoingMatch.Completed
    }
}
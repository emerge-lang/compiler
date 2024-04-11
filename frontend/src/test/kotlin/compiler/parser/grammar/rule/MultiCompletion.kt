package compiler.compiler.parser.grammar.rule

import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.OngoingMatch

class MultiCompletion : MatchingContinuation<Any> {
    val results = mutableListOf<MatchingResult<Any>>()
    override fun resume(result: MatchingResult<Any>): OngoingMatch {
        results.add(result)
        return OngoingMatch.Completed
    }
}
package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.reportings.Reporting

open class SingleTokenRule<Item : Token>(
    override val explicitName: String,

    /**
     * Like the argument to [Iterable.mapNotNull]: token of the correct type if it fits, null otherwise. Intended
     * to be used with the `as?` operator
     */
    private val filterAndCast: (Token) -> Item?,
) : Rule<Item> {
    override fun toString() = explicitName

    override fun startMatching(continueWith: MatchingContinuation<Item>): OngoingMatch = MatchImpl(continueWith)

    private inner class MatchImpl(
        val continueWith: MatchingContinuation<Item>
    ) : OngoingMatch {
        override fun toString() = "SingleTokenRule\$MatchImpl[${this@SingleTokenRule.explicitName}]"

        private lateinit var nextMatch: OngoingMatch

        override fun step(token: Token): Boolean {
            if (this::nextMatch.isInitialized) {
                return nextMatch.step(token)
            }

            val filteredToken = filterAndCast(token)
            val result: MatchingResult<Item>
            val consumed: Boolean
            if (filteredToken != null) {
                result = MatchingResult(filteredToken, emptySet())
                consumed = true
            } else {
                result = MatchingResult(null, setOf(Reporting.parsingMismatch(this@SingleTokenRule.explicitName, token)))
                consumed = false
            }
            nextMatch = continueWith.resume(result)
            return consumed
        }
    }
}


package compiler.parser.grammar.rule

import compiler.lexer.Token

class NoopRule<Item : Any>(val result: MatchingResult<Item>) : Rule<Item> {
    override val explicitName = "noop"

    override fun startMatching(continueWith: MatchingContinuation<Item>): OngoingMatch {
        return object : OngoingMatch {
            private val sub by lazy { continueWith.resume(result) }
            override fun step(token: Token): Boolean {
                return sub.step(token)
            }
        }
    }
}

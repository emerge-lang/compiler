package compiler.parser.grammar.dsl

import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.OngoingMatch
import compiler.parser.grammar.rule.Rule

object NewlineEaterRule : Rule<Unit> {
    override val explicitName: String = "0..* newlines"

    override fun startMatching(continueWith: MatchingContinuation<Unit>): OngoingMatch {
        return object : OngoingMatch {
            private lateinit var followUp: OngoingMatch
            override fun step(token: Token): Boolean {
                if (this::followUp.isInitialized) {
                    return this.followUp.step(token)
                }

                if (token is OperatorToken && token.operator == Operator.NEWLINE) {
                    return true
                }

                followUp = continueWith.resume(MatchingResult(Unit, emptySet()))
                return followUp.step(token)
            }
        }
    }
}
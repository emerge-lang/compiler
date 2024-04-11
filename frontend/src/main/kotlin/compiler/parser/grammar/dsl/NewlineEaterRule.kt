package compiler.parser.grammar.dsl

import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.OngoingMatch
import compiler.parser.grammar.rule.RepeatingRule
import compiler.parser.grammar.rule.Rule

object NewlineEaterRule : Rule<Unit> {
    override val explicitName: String = "0..* newlines"

    private val delegate = RepeatingRule(TokenEqualToRule(OperatorToken(Operator.NEWLINE)), Int.MAX_VALUE)
        .mapResult { Unit }

    override fun startMatching(continueWith: MatchingContinuation<Unit>): OngoingMatch = delegate.startMatching(continueWith)
}
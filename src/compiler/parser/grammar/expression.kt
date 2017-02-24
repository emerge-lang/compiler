package compiler.parser.grammar

import ParanthesisedExpression
import ValueExpression
import compiler.ast.expression.Expression
import compiler.parser.TokenSequence
import compiler.parser.postproc.flatten
import compiler.parser.postproc.mapResult
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule

class ExpressionRule : Rule<Expression> {
    override val descriptionOfAMatchingThing = "expression"

    override fun tryMatch(input: TokenSequence): MatchingResult<Expression> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        rule {
            eitherOf {
                ref{ParanthesisedExpression}
                ref(ValueExpression)
            }
        }
            .flatten()
            .mapResult { it.next()!! as Expression }
    }

    companion object {
        val INSTANCE = ExpressionRule()
    }
}
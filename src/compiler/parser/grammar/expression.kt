package compiler.parser.grammar

import BinaryExpression
import ExpressionPostfix
import ParanthesisedExpression
import UnaryExpression
import ValueExpression
import compiler.ast.expression.Expression
import compiler.parser.TokenSequence
import compiler.parser.postproc.ExpressionPostfixModifier
import compiler.parser.postproc.flatten
import compiler.parser.postproc.mapResult
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

class ExpressionRule : Rule<Expression<*>> {
    override val descriptionOfAMatchingThing = "expression"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<Expression<*>> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        rule {
            __matched()
            eitherOf {
                ref(BinaryExpression)
                ref(UnaryExpression)
                ref(ValueExpression)
                ref(ParanthesisedExpression)
            }
            atLeast(0) {
                ref(ExpressionPostfix)
            }
            __definitive()
        }
            .flatten()
            .mapResult(this::postprocess)
    }

    private fun postprocess(input: TransactionalSequence<Any, Position>): Expression<*> {
        var expression = input.next()!! as Expression<*>
        @Suppress("UNCHECKED_CAST")
        val postfixes = input.remainingToList() as List<ExpressionPostfixModifier<*>>

        for (postfixMod in postfixes) {
            expression = postfixMod.modify(expression)
        }

        return expression
    }

    companion object {
        val INSTANCE = ExpressionRule()
    }
}
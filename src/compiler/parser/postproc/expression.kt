package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.expression.*
import compiler.lexer.IdentifierToken
import compiler.lexer.NumericLiteralToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun LiteralExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ tokens ->
            val valueToken = tokens.next()!!

            if (valueToken is NumericLiteralToken) {
                NumericLiteralExpression(valueToken)
            }
            else {
                throw InternalCompilerError("Unsupported literal value $valueToken")
            }
        })
}

fun ValueExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({  things ->
            val valueThing = things.next()!!

            if (valueThing is Expression<*>) {
                valueThing
            }
            else if (valueThing is IdentifierToken) {
                IdentifierExpression(valueThing)
            }
            else {
                throw InternalCompilerError("Unsupported value $valueThing")
            }
        })
}

fun ParanthesisedExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ input ->
            // skip PARANT_OPEN
            input.next()!!

            input.next()!! as Expression<*>
        })
}

fun BinaryExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult { input ->
            val expressionOne = input.next()!! as Expression<*>
            val operator = (input.next()!! as OperatorToken)
            val expressionTwo = input.next()!! as Expression<*>

            BinaryExpression(expressionOne, operator, expressionTwo)
        }
}

fun UnaryExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ input ->
            val operator = (input.next()!! as OperatorToken).operator
            val expression = input.next()!! as Expression<*>
            UnaryExpression(operator, expression)
        })
}

/**
 * A postfix modifier resembles an expression postfix. Given the expression itself, it returns a new
 * expression that contains the information about the postfix. E.g. matching the !! postfix results in a
 * [NotNullExpressionPostfixModifier] which in turn will wrap any given [Expression] in a [NotNullExpression].
 */
interface ExpressionPostfixModifier<out OutExprType: Expression<*>> {
    fun modify(expr: Expression<*>): OutExprType
}

class NotNullExpressionPostfixModifier(
    /** The notnull operator for reference; whether the operator is actually [Operator.NOTNULL] is never checked.*/
    val notNullOperator: OperatorToken
) : ExpressionPostfixModifier<NotNullExpression> {
    override fun modify(expr: Expression<*>) = NotNullExpression(expr, notNullOperator)
}

class InvocationExpressionPostfixModifier(
    val parameterExpressions: List<Expression<*>>
) : ExpressionPostfixModifier<InvocationExpression> {
    override fun modify(expr: Expression<*>) = InvocationExpression(expr, parameterExpressions)

    companion object {
        fun fromMatchedTokens(input: TransactionalSequence<Any, Position>): InvocationExpressionPostfixModifier {
            // skip PARANT_OPEN
            input.next()!! as OperatorToken

            val paramExpressions = mutableListOf<Expression<*>>()
            while (input.peek() is Expression<*>) {
                paramExpressions.add(input.next()!! as Expression<*>)

                // skip COMMA or PARANT_CLOSE
                input.next()!! as OperatorToken
            }

            return InvocationExpressionPostfixModifier(paramExpressions)
        }
    }
}

class MemberAccessExpressionPostfixModifier(
    val memberName: IdentifierToken
) : ExpressionPostfixModifier<MemberAccessExpression> {
    override fun modify(expr: Expression<*>) = MemberAccessExpression(expr, memberName)
}
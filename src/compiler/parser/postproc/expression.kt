package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.expression.*
import compiler.lexer.IdentifierToken
import compiler.lexer.NumericLiteralToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun LiteralExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult(allowPostfixNotnull { tokens ->
            val valueToken = tokens.next()!!

            if (valueToken is NumericLiteralToken) {
                NumericLiteralExpression(valueToken)
            }
            else {
                throw InternalCompilerError("Unsupported literal value $valueToken")
            }
        })
}

fun ValueExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult(allowPostfixNotnull {  things ->
            val valueThing = things.next()!!

            if (valueThing is Expression) {
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

fun ParanthesisedExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult(allowPostfixNotnull { input ->
            // skip PARANT_OPEN
            input.next()!!

            input.next()!! as Expression
        })
}

fun BinaryExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { input ->
            val expressionOne = input.next()!! as Expression
            val operator = (input.next()!! as OperatorToken)
            val expressionTwo = input.next()!! as Expression

            BinaryExpression(expressionOne, operator, expressionTwo)
        }
}

fun UnaryExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult(allowPostfixNotnull { input ->
            val operator = (input.next()!! as OperatorToken).operator
            val expression = input.next()!! as Expression
            UnaryExpression(operator, expression)
        })
}

private fun allowPostfixNotnull(mapper: (TransactionalSequence<Any, Position>) -> Expression): (TransactionalSequence<Any, Position>) -> Expression {
    return { input ->
        val expression = mapper(input)
        if (input.peek() == OperatorToken(Operator.NOTNULL)) {
            NotNullExpression(expression, input.next()!! as OperatorToken)
        }
        else {
            expression
        }
    }
}
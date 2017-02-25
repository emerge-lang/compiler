package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.expression.*
import compiler.lexer.IdentifierToken
import compiler.lexer.NumericLiteralToken
import compiler.lexer.OperatorToken
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule

fun LiteralExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { tokens ->
            val valueToken = tokens.next()!!

            if (valueToken is NumericLiteralToken) {
                NumericLiteralExpression(valueToken)
            }
            else {
                throw InternalCompilerError("Unsupported literal value $valueToken")
            }
        }
}

fun ValueExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { things ->
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
        }
}

fun ParanthesisedExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { input ->
            // skip PARANT_OPEN
            input.next()!!

            input.next()!! as Expression
        }
}

fun PostfixExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { input ->
            val expression = input.next()!! as Expression
            val postfixOp = input.next()!! as OperatorToken

            PostfixExpression(expression, postfixOp)
        }
}

fun AryExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { input ->
            val expressionOne = input.next()!! as Expression
            val operator = (input.next()!! as OperatorToken)
            val expressionTwo = input.next()!! as Expression

            AryExpression(expressionOne, operator, expressionTwo)
        }
}

fun UnaryExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten()
        .mapResult { input ->
            val operator = (input.next()!! as OperatorToken).operator
            val expression = input.next()!! as Expression
            UnaryExpression(operator, expression)
        }
}


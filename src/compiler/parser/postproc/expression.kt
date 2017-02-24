package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.expression.Expression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.NumericLiteralToken
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
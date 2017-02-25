package compiler.ast.expression

import compiler.lexer.OperatorToken

class PostfixExpression(
    val expression: Expression,
    val postfixOp: OperatorToken
) : Expression
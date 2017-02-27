package compiler.ast.expression

import compiler.lexer.OperatorToken

class BinaryExpression(
    val first: Expression,
    val op: OperatorToken,
    val second: Expression
) : Expression
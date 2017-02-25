package compiler.ast.expression

import compiler.lexer.OperatorToken

class AryExpression(
    val first: Expression,
    val op: OperatorToken,
    val second: Expression
) : Expression
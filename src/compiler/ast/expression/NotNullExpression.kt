package compiler.ast.expression

import compiler.lexer.OperatorToken

/** A not-null enforcement expression created by the !! operator */
class NotNullExpression(
    val nullableExpression: Expression,
    val notNullOperator: OperatorToken
) : Expression

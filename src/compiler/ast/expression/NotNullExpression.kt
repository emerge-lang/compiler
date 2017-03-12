package compiler.ast.expression

import compiler.ast.context.CTContext
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.TypeReference
import compiler.lexer.OperatorToken

/** A not-null enforcement expression created by the !! operator */
class NotNullExpression(
    val nullableExpression: Expression,
    val notNullOperator: OperatorToken
) : Expression
{
    override val sourceLocation = nullableExpression.sourceLocation

    override fun determineType(context: CTContext): BaseTypeReference? {
        return nullableExpression.determineType(context)?.nonNull()
    }
}
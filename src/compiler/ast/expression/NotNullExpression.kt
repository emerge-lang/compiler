package compiler.ast.expression

import compiler.ast.context.CTContext
import compiler.ast.type.TypeReference
import compiler.lexer.OperatorToken

/** A not-null enforcement expression created by the !! operator */
class NotNullExpression(
    val nullableExpression: Expression,
    val notNullOperator: OperatorToken
) : Expression
{
    override fun determinedType(context: CTContext): TypeReference {
        return nullableExpression.determinedType(context).nonNull()
    }
}
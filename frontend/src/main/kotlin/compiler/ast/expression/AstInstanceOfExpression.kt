package compiler.ast.expression

import compiler.ast.Expression
import compiler.ast.type.TypeReference
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundInstanceOfExpression
import compiler.lexer.KeywordToken

class AstInstanceOfExpression(
    val expressionToCheck: Expression,
    val operator: KeywordToken,
    val typeToCheck: TypeReference,
) : Expression {
    override val span = expressionToCheck.span .. (typeToCheck.span ?: operator.span)

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val boundExpr = expressionToCheck.bindTo(context)
        return BoundInstanceOfExpression(
            boundExpr.modifiedContext,
            this,
            boundExpr,
        )
    }
}
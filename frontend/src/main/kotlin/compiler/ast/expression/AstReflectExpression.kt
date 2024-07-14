package compiler.ast.expression

import compiler.ast.Expression
import compiler.ast.type.TypeReference
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundReflectExpression
import compiler.lexer.KeywordToken

class AstReflectExpression(
    val keyword: KeywordToken,
    val type: TypeReference,
) : Expression {
    override val span = type.span?.let { typeSpan -> keyword.span .. typeSpan } ?: keyword.span

    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return BoundReflectExpression(context, this)
    }
}
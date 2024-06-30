package compiler.ast.expression

import compiler.ast.Expression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundTopLevelFunctionReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Span

class AstTopLevelFunctionReference(
    override val span: Span,
    val nameToken: IdentifierToken,
) : Expression {
    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        return BoundTopLevelFunctionReference(
            context,
            this,
        )
    }
}
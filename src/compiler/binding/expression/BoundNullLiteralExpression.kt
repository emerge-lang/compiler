package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.NullLiteralExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.lexer.SourceLocation

class BoundNullLiteralExpression(
    override val context: CTContext,
    override val declaration: NullLiteralExpression
) : BoundExpression<NullLiteralExpression>
{
    override val type: BaseTypeReference? = null

    override val isGuaranteedToThrow = null

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet()

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet()

    companion object {
        fun getInstance(context: CTContext, sourceLocation: SourceLocation = SourceLocation.UNKNOWN) =
            BoundNullLiteralExpression(
                context,
                NullLiteralExpression(sourceLocation)
            )
    }
}

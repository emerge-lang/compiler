package compiler.binding.expression

import compiler.ast.expression.NullLiteralExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.lexer.SourceLocation

class BoundNullLiteralExpression(
    override val context: CTContext,
    override val declaration: NullLiteralExpression
) : BoundExpression<NullLiteralExpression>
{
    override val type: BaseTypeReference? = null

    companion object {
        fun getInstance(context: CTContext, sourceLocation: SourceLocation = SourceLocation.UNKNOWN) =
            BoundNullLiteralExpression(
                context,
                NullLiteralExpression(sourceLocation)
            )
    }
}

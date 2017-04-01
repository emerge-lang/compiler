package compiler.binding.expression

import compiler.ast.expression.UnaryExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundUnaryExpression(
    override val context: CTContext,
    override val declaration: UnaryExpression,
    override val type: BaseTypeReference?,
    val orginal: BoundExpression<*>
) : BoundExpression<UnaryExpression>
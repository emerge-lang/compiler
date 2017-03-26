package compiler.binding.expression

import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundNotNullExpression(
    override val context: CTContext,
    override val declaration: NotNullExpression,
    override val type: BaseTypeReference?,
    val nullableExpression: BoundExpression<*>
) : BoundExpression<NotNullExpression>, BoundExecutable<NotNullExpression>
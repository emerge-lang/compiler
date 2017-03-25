package compiler.binding.expression

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundInvocationExpression(
    override val context: CTContext,
    override val declaration: InvocationExpression,
    override val type: BaseTypeReference?
) : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression>

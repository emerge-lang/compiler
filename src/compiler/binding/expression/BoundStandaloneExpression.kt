package compiler.binding.expression

import compiler.ast.expression.StandaloneExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundStandaloneExpression(
    override val context: CTContext,
    override val declaration: StandaloneExpression,
    override val type: BaseTypeReference?,
    val original: BoundExpression<*>
) : BoundExpression<StandaloneExpression>, BoundExecutable<StandaloneExpression>
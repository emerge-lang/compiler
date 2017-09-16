package compiler.binding.expression

import compiler.ast.expression.IfExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundIfExpression(
    override val context: CTContext,
    override val declaration: IfExpression,
    val condition: BoundExpression<*>,
    val thenCode: BoundExecutable<*>,
    val elseCode: BoundExecutable<*>?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override val isGuaranteedToThrow: Boolean?
        get() = (thenCode?.isGuaranteedToThrow ?: false) and (elseCode?.isGuaranteedToThrow ?: false)

    override val isGuaranteedToReturn: Boolean?
        get() = (thenCode?.isGuaranteedToReturn ?: false) and (elseCode?.isGuaranteedToReturn ?: false)

    override var type: BaseTypeReference? = null
        private set
}
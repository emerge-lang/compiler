package compiler.binding.expression

import compiler.ast.expression.BooleanLiteralExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.BuiltinBoolean

class BoundBooleanLiteralExpression(
    override val context: CTContext,
    override val declaration: BooleanLiteralExpression,
    val value: Boolean
) : BoundExpression<BooleanLiteralExpression> {
    override val type: BaseTypeReference = BuiltinBoolean.baseReference(context)

    override val isGuaranteedToThrow: Boolean = false
}
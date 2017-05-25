package compiler.binding.expression

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundMemberAccessExpression(
    override val context: CTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: BaseTypeReference? = null
        private set
}
package compiler.binding.expression

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundMemberAccessExpression(
    override val context: CTContext,
    override val declaration: MemberAccessExpression,

    /**
     * The type of this expression. Is null if there is no such member variable on the type of [valueExpression]
     */
    override val type: BaseTypeReference?,

    val valueExpression: BoundExpression<*>,
    val memberName: String
) : BoundExpression<MemberAccessExpression>
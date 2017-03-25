package compiler.binding.expression

import compiler.ast.expression.IdentifierExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression,
    override val type: BaseTypeReference?
) : BoundExpression<IdentifierExpression>

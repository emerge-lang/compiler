package compiler.binding.expression

import compiler.ast.expression.Expression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

interface BoundExpression<out ASTType> {
    /**
     * The context this expression has been bound to.
     */
    val context: CTContext

    /**
     * The [Expression] that was bound to [context].
     */
    val declaration: ASTType

    /**
     * The type of this expression when evaluated If the type could not be determined due to semantic errors,
     * this might be a close guess or null.
     */
    val type: BaseTypeReference?
}
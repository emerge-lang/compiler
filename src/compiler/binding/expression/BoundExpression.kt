package compiler.binding.expression

import compiler.binding.BoundExecutable
import compiler.binding.type.BaseTypeReference

interface BoundExpression<out ASTType> : BoundExecutable<ASTType> {
    /**
     * The type of this expression when evaluated If the type could not be determined due to semantic errors,
     * this might be a close guess or null.
     */
    val type: BaseTypeReference?
}
package compiler.binding

import compiler.ast.VariableDeclaration
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

/**
 * Describes the presence/avaiability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: CTContext,
    override val declaration: VariableDeclaration,
    val type: BaseTypeReference?
) : BoundExecutable<VariableDeclaration>
{
    val isAssignable: Boolean = declaration.isAssignable

    val name: String = declaration.name.value
}
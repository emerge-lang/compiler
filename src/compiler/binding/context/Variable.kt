package compiler.binding.context

import compiler.ast.VariableDeclaration
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.TypeReference

/**
 * Describes the presence/avaiability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class Variable(val context: CTContext, val declaration: VariableDeclaration, type: TypeReference? = null)
{
    val type: BaseTypeReference? by lazy {
        type?.resolveWithin(context) ?: declaration.determineType(context)
    }

    val isAssignable: Boolean = declaration.isAssignable
}
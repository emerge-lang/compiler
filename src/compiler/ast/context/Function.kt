package compiler.ast.context

import compiler.ast.FunctionDeclaration
import compiler.ast.type.Any
import compiler.ast.type.BaseType
import compiler.ast.type.BaseTypeReference

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
class Function(val context: CTContext, val declaration: FunctionDeclaration) {
    val returnType: BaseTypeReference
        get() = declaration.returnType.resolveWithin(context) ?: Any.baseReference(context)
}
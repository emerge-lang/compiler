package compiler.ast

import compiler.ast.type.TypeReference
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext

class ParameterList (
    val parameters: List<VariableDeclaration> = emptyList()
) : Bindable<BoundParameterList> {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }

    override fun bindTo(context: CTContext) = BoundParameterList(
        context,
        this,
        parameters.map { it.bindTo(context) }
    )
}
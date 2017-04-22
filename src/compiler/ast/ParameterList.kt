package compiler.ast

import compiler.ast.type.TypeReference
import compiler.binding.BindingResult
import compiler.binding.BoundParameter
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.parser.Reporting

class ParameterList (
    val parameters: List<VariableDeclaration> = emptyList()
) : Bindable<BoundParameterList> {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }

    fun bindTo(context: CTContext, allowUntyped: Boolean = true): BindingResult<BoundParameterList> {
        val reportings = mutableListOf<Reporting>()

        val boundParams = mutableListOf<BoundParameter>()
        parameters.forEach { param ->
            val boundParamResult = param.bindTo(context)
            val boundParam = boundParamResult.bound

            // double names
            if (boundParams.find { it.name == boundParam.name } != null) {
                reportings.add(Reporting.error("BoundParameter ${param.name.value} is already defined in the parameter list", param.name))
            }
            else {
                boundParams.add(boundParam)
            }

            if (!allowUntyped && param.type == null) {
                reportings.add(Reporting.error("The type of parameter ${param.name.value} must be explicitly declared.", param.declaredAt))
            }

            // etc.
            reportings.addAll(boundParamResult.reportings)
        }

        return BindingResult(
            BoundParameterList(
                context,
                this,
                boundParams
            ),
            reportings
        )
    }

    override fun bindTo(context: CTContext) = bindTo(context, false)
}
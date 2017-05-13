package compiler.binding

import compiler.ast.ParameterList
import compiler.binding.context.CTContext
import compiler.parser.Reporting

class BoundParameterList(
    val context: CTContext,
    val declaration: ParameterList,
    val parameters: List<BoundParameter>
) {
    fun semanticAnalysisPhase1(allowUntyped: Boolean = true): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // double names
        for (param in parameters) {
            if (parameters.find { it !== param && it.name == param.name } != null) {
                reportings.add(Reporting.error("BoundParameter ${param.name} is already defined in the parameter list", param.declaration.declaredAt))
            }

            if (!allowUntyped && param.declaration.type == null) {
                reportings.add(Reporting.error("The type of parameter ${param.name} must be explicitly declared.", param.declaration.declaredAt))
            }

            // etc.
            reportings.addAll(param.semanticAnalysisPhase1("parameter"))
        }

        return reportings
    }
}

typealias BoundParameter = BoundVariable
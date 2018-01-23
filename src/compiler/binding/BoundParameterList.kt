package compiler.binding

import compiler.ast.ParameterList
import compiler.binding.context.CTContext
import compiler.reportings.Reporting

class BoundParameterList(
    val context: CTContext,
    val declaration: ParameterList,
    val parameters: List<BoundParameter>
) {
    fun semanticAnalysisPhase1(allowUntyped: Boolean = true): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        parameters.forEachIndexed { index, parameter ->
            // double names
            if (index > 0) {
                val previousWithSameName = parameters.subList(0, index).find { it !== parameter && it.name == parameter.name }
                if (previousWithSameName != null) {
                    reportings.add(Reporting.error("Parameter ${parameter.name} has already been defined in ${previousWithSameName.declaration.sourceLocation.fileLineColumnText}", parameter.declaration.declaredAt))
                }
            }

            if (!allowUntyped && parameter.declaration.type == null) {
                reportings.add(Reporting.error("The type of parameter ${parameter.name} must be explicitly declared.", parameter.declaration.declaredAt))
            }

            // etc.
            reportings.addAll(parameter.semanticAnalysisPhase1("parameter"))
        }

        return reportings
    }
}

typealias BoundParameter = BoundVariable
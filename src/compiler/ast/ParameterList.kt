package compiler.ast

import compiler.ast.context.CTContext
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.parser.Reporting
import java.util.*

class ParameterList (
    val parameters: List<VariableDeclaration> = emptyList()
) {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }

    fun validate(context: CTContext, allowUntyped: Boolean = true): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        val knownNames = HashSet<String>()
        parameters.forEach { param ->
            // double names
            if (knownNames.contains(param.name.value)) {
                reportings.add(Reporting.error("Parameter ${param.name.value} is already defined in the parameter list", param.name))
            }
            else {
                knownNames.add(param.name.value)
            }

            // etc.
            reportings.addAll(param.validate(context, "parameter"))
        }

        return reportings
    }
}
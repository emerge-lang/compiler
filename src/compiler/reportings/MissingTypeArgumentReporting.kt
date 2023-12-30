package compiler.reportings

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeParameter
import compiler.lexer.SourceLocation

data class MissingTypeArgumentReporting(
    val parameter: TypeParameter,
    val lastSuppliedArgument: TypeArgument,
) : Reporting(
    Level.ERROR,
    "No argument supplied for type parameter ${parameter.name.value}",
    lastSuppliedArgument.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun toString() = super.toString()
}
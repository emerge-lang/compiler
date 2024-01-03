package compiler.reportings

import compiler.ast.type.TypeParameter
import compiler.lexer.SourceLocation

class MissingTypeArgumentReporting(
    val parameter: TypeParameter,
    sourceLocation: SourceLocation,
) : Reporting(
    Level.ERROR,
    "No argument supplied for type parameter ${parameter.name.value}",
    sourceLocation,
) {
    override fun toString() = super.toString()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MissingTypeArgumentReporting) return false

        if (parameter != other.parameter) return false
        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = parameter.hashCode()
        result = result * 31 + sourceLocation.hashCode()
        return result
    }
}
package compiler.reportings

import compiler.ast.type.TypeParameter

class VarianceOnFunctionTypeParameterReporting(
    val parameter: TypeParameter,
) : Reporting(
    Level.ERROR,
    "Type parameters on functions cannot have variance",
    parameter.name.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as VarianceOnFunctionTypeParameterReporting

        return parameter == other.parameter && parameter.bound?.span == other.parameter.bound?.span
    }

    override fun hashCode(): Int {
        var result = parameter.hashCode()
        result = result * 31 + parameter.bound?.span.hashCode()
        return result
    }
}
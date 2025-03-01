package compiler.diagnostic

import compiler.ast.type.TypeParameter

class VarianceOnFunctionTypeParameterDiagnostic(
    val parameter: TypeParameter,
) : Diagnostic(
    Level.ERROR,
    "Type parameters on functions cannot have variance",
    parameter.name.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as VarianceOnFunctionTypeParameterDiagnostic

        return parameter == other.parameter && parameter.bound?.span == other.parameter.bound?.span
    }

    override fun hashCode(): Int {
        var result = parameter.hashCode()
        result = result * 31 + parameter.bound?.span.hashCode()
        return result
    }
}
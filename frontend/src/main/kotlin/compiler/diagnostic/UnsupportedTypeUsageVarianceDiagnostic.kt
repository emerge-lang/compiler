package compiler.diagnostic

import compiler.ast.type.TypeVariance
import compiler.binding.type.TypeUseSite

class UnsupportedTypeUsageVarianceDiagnostic(
    val useSite: TypeUseSite,
    val erroneousVariance: TypeVariance,
) : Diagnostic(
    Severity.ERROR,
    "Cannot use an ${erroneousVariance.description} type in an ${useSite.varianceDescription} location",
    useSite.usageLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as UnsupportedTypeUsageVarianceDiagnostic

        if (useSite != other.useSite) return false
        if (erroneousVariance != other.erroneousVariance) return false

        return true
    }

    override fun hashCode(): Int {
        var result = useSite.hashCode()
        result = 31 * result + erroneousVariance.hashCode()
        return result
    }
}

private val TypeVariance.description: String get() = if (this == TypeVariance.UNSPECIFIED) "invariant" else this.toString()
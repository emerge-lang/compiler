package compiler.diagnostic

import compiler.binding.DefinitionWithVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Span

class HiddenTypeExposedDiagnostic(
    val type: BoundBaseType,
    val exposedBy: DefinitionWithVisibility,
    exposedAt: Span,
) : Diagnostic(
    Severity.ERROR,
    run {
        val typeName = type.simpleName
        val exposedByStr = exposedBy.toStringForErrorMessage()
        val prefixLength = typeName.length.coerceAtLeast(exposedByStr.length)

        val paddedTypeName = typeName.padEnd(prefixLength, ' ')
        val paddedExposedBy = exposedByStr.padEnd(prefixLength, ' ')

        """
            ${exposedBy.toStringForErrorMessage()} exposes the more restricted type $typeName:
            $paddedTypeName is ${type.visibility},
            $paddedExposedBy is ${exposedBy.visibility}
        """.trimIndent()
    },
    exposedAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is HiddenTypeExposedDiagnostic) return false

        if (type != other.type) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = type.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}
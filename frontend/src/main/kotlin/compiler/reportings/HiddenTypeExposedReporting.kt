package compiler.reportings

import compiler.binding.DefinitionWithVisibility
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.lexer.SourceLocation

class HiddenTypeExposedReporting(
    val type: BoundBaseTypeDefinition,
    val exposedBy: DefinitionWithVisibility,
    exposedAt: SourceLocation,
) : Reporting(
    Level.ERROR,
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
        if (other !is HiddenTypeExposedReporting) return false

        if (type != other.type) return false
        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = type.hashCode()
        result = 31 * result + sourceLocation.hashCode()
        return result
    }
}
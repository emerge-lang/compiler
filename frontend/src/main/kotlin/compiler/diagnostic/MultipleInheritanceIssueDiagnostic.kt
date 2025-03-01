package compiler.diagnostic

import compiler.binding.basetype.BoundBaseType
import textutils.assureEndsWith

class MultipleInheritanceIssueDiagnostic(
    val base: Diagnostic,
    val contributingSuperTypes: Collection<BoundBaseType>,
    val conflictOnSubType: BoundBaseType,
) : Diagnostic(
    base.severity,
    run {
        val supertypeList = contributingSuperTypes.joinToString(
            transform = { it.canonicalName.simpleName },
            separator = ", "
        )
        "The multiple inheritance ${conflictOnSubType.simpleName} : $supertypeList creates this problem:"
    },
    base.span,
) {
    override fun toString() = "${levelAndMessage.assureEndsWith('\n')}${base}"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MultipleInheritanceIssueDiagnostic) return false
        if (!super.equals(other)) return false

        if (base != other.base) return false
        if (conflictOnSubType != other.conflictOnSubType) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + base.hashCode()
        result = 31 * result + conflictOnSubType.hashCode()
        return result
    }
}
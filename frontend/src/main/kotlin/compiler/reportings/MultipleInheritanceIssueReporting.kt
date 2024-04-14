package compiler.reportings

import compiler.binding.type.BaseType
import textutils.assureEndsWith

class MultipleInheritanceIssueReporting(
    val base: Reporting,
    val contributingSuperTypes: Collection<BaseType>,
    val conflictOnSubType: BaseType,
) : Reporting(
    base.level,
    run {
        val supertypeList = contributingSuperTypes.joinToString(
            transform = { it.canonicalName.simpleName },
            separator = ", "
        )
        "The multiple inheritance ${conflictOnSubType.simpleName} : $supertypeList creates this problem:"
    },
    base.sourceLocation,
) {
    override fun toString() = "${levelAndMessage.assureEndsWith('\n')}${base}"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MultipleInheritanceIssueReporting) return false
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
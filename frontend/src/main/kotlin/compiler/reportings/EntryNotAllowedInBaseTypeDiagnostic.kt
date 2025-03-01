package compiler.reportings

import compiler.InternalCompilerError
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeEntry
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import textutils.capitalizeFirst

class EntryNotAllowedInBaseTypeDiagnostic(
    val typeKind: BoundBaseType.Kind,
    val violatingEntry: BoundBaseTypeEntry<*>,
) : Diagnostic(
    Level.ERROR,
    run {
        val entryDesc = when (violatingEntry) {
            is BoundClassConstructor -> "constructors"
            is BoundClassDestructor -> "destructors"
            is BoundBaseTypeMemberVariable -> "member variables"
            else -> throw InternalCompilerError("The base type entry ${violatingEntry::class.simpleName} should be allowed in all base types")
        }
        "${entryDesc.capitalizeFirst()} are not allowed in ${typeKind.namePlural}"
    },
    violatingEntry.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is EntryNotAllowedInBaseTypeDiagnostic) return false

        if (violatingEntry.declaredAt != other.violatingEntry.declaredAt) return false

        return true
    }

    override fun hashCode(): Int {
        return violatingEntry.declaredAt.hashCode()
    }
}
package compiler.reportings

import compiler.InternalCompilerError
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.binding.basetype.BoundBaseTypeEntry
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.basetype.BoundClassDestructor
import textutils.capitalizeFirst

class EntryNotAllowedInBaseTypeReporting(
    val typeKind: BoundBaseTypeDefinition.Kind,
    val violatingEntry: BoundBaseTypeEntry<*>,
) : Reporting(
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
    violatingEntry.declaration.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is EntryNotAllowedInBaseTypeReporting) return false

        if (violatingEntry.declaration.declaredAt != other.violatingEntry.declaration.declaredAt) return false

        return true
    }

    override fun hashCode(): Int {
        return violatingEntry.declaration.declaredAt.hashCode()
    }
}
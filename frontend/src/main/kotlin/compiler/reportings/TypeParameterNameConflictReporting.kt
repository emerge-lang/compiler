package compiler.reportings

import compiler.InternalCompilerError
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.SourceLocation

class TypeParameterNameConflictReporting(
    val originalType: BoundTypeReference,
    val conflicting: BoundTypeParameter,
) : Reporting(
    Level.ERROR,
    run {
        "A type with name ${conflicting.name} is already defined in this context"
    },
    conflicting.astNode.name.sourceLocation,
) {
    override fun toString(): String {
        val originalReference = when (originalType) {
            is RootResolvedTypeReference -> originalType.baseType.baseReference.sourceLocation ?: SourceLocation.UNKNOWN
            is GenericTypeReference -> originalType.parameter.astNode.name.sourceLocation
            else -> throw InternalCompilerError("This should be impossible")
        }

        return super.toString() + "\n${conflicting.name} is already defined in $originalReference"
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeParameterNameConflictReporting) return false

        if (conflicting.astNode.name.sourceLocation != other.conflicting.astNode.name.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return conflicting.astNode.name.sourceLocation.hashCode()
    }
}
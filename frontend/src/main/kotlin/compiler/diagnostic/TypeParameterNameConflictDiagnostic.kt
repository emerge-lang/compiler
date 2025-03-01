package compiler.diagnostic

import compiler.InternalCompilerError
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.Span

class TypeParameterNameConflictDiagnostic(
    val originalType: BoundTypeReference,
    val conflicting: BoundTypeParameter,
) : Diagnostic(
    Severity.ERROR,
    run {
        "A type with name ${conflicting.name} is already defined in this context"
    },
    conflicting.astNode.name.span,
) {
    override fun toString(): String {
        val originalReference = when (originalType) {
            is RootResolvedTypeReference -> originalType.baseType.baseReference.span ?: Span.UNKNOWN
            is GenericTypeReference -> originalType.parameter.astNode.name.span
            else -> throw InternalCompilerError("This should be impossible")
        }

        return super.toString() + "\n${conflicting.name} is already defined in $originalReference"
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeParameterNameConflictDiagnostic) return false

        if (conflicting.astNode.name.span != other.conflicting.astNode.name.span) return false

        return true
    }

    override fun hashCode(): Int {
        return conflicting.astNode.name.span.hashCode()
    }
}
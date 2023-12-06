package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class ModifiedTypeReference(
    override val context: CTContext,
    val base: ResolvedTypeReference,
    val modifications: TypeReference,
) : ResolvedTypeReference {
    override val isNullable get() = when(modifications.nullability) {
        TypeReference.Nullability.NOT_NULLABLE -> false
        TypeReference.Nullability.NULLABLE -> true
        TypeReference.Nullability.UNSPECIFIED -> base.isNullable
    }

    override val simpleName get() = base.simpleName
    override val mutability get() = modifications.mutability ?: base.mutability

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return ModifiedTypeReference(context, base, modifications.withMutability(modifier))
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        TODO()
    }

    override fun validate(): Collection<Reporting> {
        // TODO

        // generic types cannot have parameters

        // mutability conflict

        // variance conflict

        return emptyList()
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        // TODO
        return null
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? {
        // TODO
        return null
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        return TODO()
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        return TODO()
    }
}
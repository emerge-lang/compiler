package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class GenericTypeReference(
    override val context: CTContext,
    private val parameter: TypeParameter,
    private val resolvedBound: ResolvedTypeReference,
) : ResolvedTypeReference {
    override val simpleName get() = parameter.name.value
    override val isNullable get() = resolvedBound.isNullable
    override val mutability get() = resolvedBound.mutability

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            resolvedBound.modifiedWith(modifier),
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            resolvedBound.withCombinedMutability(mutability),
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            resolvedBound.withCombinedNullability(nullability),
        )
    }

    override fun validate(): Collection<Reporting> {
        // TODO
        return emptySet()
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        TODO("Not yet implemented")
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return other is GenericTypeReference && this.parameter === other.parameter
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? {
        TODO("Not yet implemented")
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun contextualize(
        context: TypeUnification,
        side: (TypeUnification) -> Map<String, BoundTypeArgument>,
    ): ResolvedTypeReference {
        val resolvedSelf = side(context)[this.simpleName] ?: return GenericTypeReference(
            this.context,
            parameter,
            resolvedBound.contextualize(context, side),
        )

        return resolvedSelf.type.contextualize(context, side)
    }

    override fun toString() = "${parameter.name.value} : $resolvedBound"
}
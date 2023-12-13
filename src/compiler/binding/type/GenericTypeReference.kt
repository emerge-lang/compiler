package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class GenericTypeReference(
    override val context: CTContext,
    private val parameter: TypeParameter,
    val bound: ResolvedTypeReference,
) : ResolvedTypeReference {
    override val simpleName get() = parameter.name.value
    override val isNullable get() = bound.isNullable
    override val mutability get() = bound.mutability

    val variance: TypeVariance get() = parameter.variance

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            bound.modifiedWith(modifier),
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            bound.withCombinedMutability(mutability),
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            parameter,
            bound.withCombinedNullability(nullability),
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
        if (mutability == null) {
            return this
        }

        return GenericTypeReference(
            context,
            parameter,
            bound.defaultMutabilityTo(mutability),
        )
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
            bound.contextualize(context, side),
        )

        return resolvedSelf.contextualize(context, side)
    }

    override fun toString() = "${parameter.name.value} : $bound"
}
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
        val selfEffective = when(variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> bound
            TypeVariance.IN -> return Reporting.valueNotAssignable(other, this, "Cannot assign an in-variant value, because it cannot be read", assignmentLocation)
        }

        return when (other) {
            is RootResolvedTypeReference -> selfEffective.evaluateAssignabilityTo(other, assignmentLocation)
            is BoundTypeArgument -> when(other.variance) {
                TypeVariance.UNSPECIFIED,
                TypeVariance.IN -> selfEffective.evaluateAssignabilityTo(other.type, assignmentLocation)
                TypeVariance.OUT -> Reporting.valueNotAssignable(other, this, "Cannot assign to an out-variant reference", assignmentLocation)
            }
            is GenericTypeReference -> when(other.variance) {
                TypeVariance.UNSPECIFIED,
                TypeVariance.IN -> selfEffective.evaluateAssignabilityTo(other.bound, assignmentLocation)
                TypeVariance.OUT -> Reporting.valueNotAssignable(other, this, "Cannot assign to an out-variant reference", assignmentLocation)
            }
            is UnresolvedType -> selfEffective.evaluateAssignabilityTo(other.standInType, assignmentLocation)
        }
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
        val selfEffective = when(variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> bound
            TypeVariance.IN -> BuiltinNothing.baseReference(context)
        }

        return when (other) {
            is RootResolvedTypeReference -> selfEffective.closestCommonSupertypeWith(other)
            is GenericTypeReference -> selfEffective.closestCommonSupertypeWith(other)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is UnresolvedType -> selfEffective.closestCommonSupertypeWith(other.standInType)
        }
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

    override fun toString() = parameter.name.value
}
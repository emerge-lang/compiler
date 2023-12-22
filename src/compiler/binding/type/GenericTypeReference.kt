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
    private val original: TypeReference,
    private val parameter: TypeParameter,
    val effectiveBound: ResolvedTypeReference,
) : ResolvedTypeReference {
    override val simpleName get() = parameter.name.value
    override val isNullable get() = effectiveBound.isNullable
    override val mutability get() = effectiveBound.mutability
    override val sourceLocation get() = original.declaringNameToken?.sourceLocation
    val variance: TypeVariance get() = parameter.variance

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            original,
            parameter,
            effectiveBound.modifiedWith(modifier),
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            original,
            parameter,
            effectiveBound.withCombinedMutability(mutability),
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        return GenericTypeReference(
            context,
            original,
            parameter,
            effectiveBound.withCombinedNullability(nullability),
        )
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        // TODO: variance mismatches?
        return effectiveBound.validate(forUsage) + setOfNotNull(forUsage.validateForTypeVariance(variance))
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        val selfEffective = when(variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> effectiveBound
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
                TypeVariance.IN -> selfEffective.evaluateAssignabilityTo(other.effectiveBound, assignmentLocation)
                TypeVariance.OUT -> Reporting.valueNotAssignable(other, this, "Cannot assign to an out-variant reference", assignmentLocation)
            }
            is UnresolvedType -> selfEffective.evaluateAssignabilityTo(other.standInType, assignmentLocation)
        }
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return other is GenericTypeReference && this.parameter === other.parameter
    }

    override fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification {
        return when (other) {
            is RootResolvedTypeReference,
            is UnresolvedType -> carry.plusLeft(simpleName, BoundTypeArgument(context, null, TypeVariance.UNSPECIFIED, other))
            is BoundTypeArgument -> carry.plusLeft(simpleName, other)
            is GenericTypeReference -> TODO("namespace conflict :(")
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        if (mutability == null) {
            return this
        }

        return GenericTypeReference(
            context,
            original,
            parameter,
            effectiveBound.defaultMutabilityTo(mutability),
        )
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        val selfEffective = when(variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> effectiveBound
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
            original,
            parameter,
            effectiveBound.contextualize(context, side),
        )

        return resolvedSelf.contextualize(context, side)
    }

    override fun toString(): String {
        var str = parameter.name.value
        if (!isNullable) {
            if (original.nullability == TypeReference.Nullability.NOT_NULLABLE) {
                str += "!"
            }
        } else if (original.nullability == TypeReference.Nullability.NULLABLE) {
            str += "?"
        }

        return str
    }
}
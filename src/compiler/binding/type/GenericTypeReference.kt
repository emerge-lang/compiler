package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

sealed class GenericTypeReference : ResolvedTypeReference {
    abstract val original: TypeReference
    abstract val parameter: BoundTypeParameter
    abstract val effectiveBound: ResolvedTypeReference

    override val simpleName get() = parameter.name
    override val isNullable get() = effectiveBound.isNullable
    override val mutability get() = effectiveBound.mutability
    override val sourceLocation get() = original.declaringNameToken?.sourceLocation
    override val inherentTypeBindings = TypeUnification.EMPTY
    val variance: TypeVariance get() = parameter.variance

    override fun withMutability(modifier: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.withMutability(modifier) }
    }

    override fun withCombinedMutability(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.withCombinedMutability(mutability) }
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): GenericTypeReference {
        return mapEffectiveBound { it.withCombinedNullability(nullability) }
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
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
            is UnresolvedType -> carry.plusLeft(simpleName, other)
            is BoundTypeArgument -> carry.plusLeft(simpleName, other)
            is GenericTypeReference -> TODO("namespace conflict :(")
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.defaultMutabilityTo(mutability) }
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
        side: (TypeUnification) -> Map<String, ResolvedTypeReference>,
    ): ResolvedTypeReference {
        val resolvedSelf = side(context)[this.simpleName] ?: return ResolvedBoundGenericTypeReference(
            this.context,
            original,
            parameter,
            effectiveBound.contextualize(context, side),
        )

        return resolvedSelf.contextualize(context, side)
    }

    private fun mapEffectiveBound(mapper: (ResolvedTypeReference) -> ResolvedTypeReference): MappedEffectiveBoundGenericTypeReference {
        return MappedEffectiveBoundGenericTypeReference(this, mapper)
    }

    override fun toString(): String {
        var str = parameter.name
        if (!isNullable) {
            if (original.nullability == TypeReference.Nullability.NOT_NULLABLE) {
                str += "!"
            }
        } else if (original.nullability == TypeReference.Nullability.NULLABLE) {
            str += "?"
        }

        return str
    }

    companion object {
        operator fun invoke(context: CTContext, original: TypeReference, parameter: BoundTypeParameter): GenericTypeReference {
            return NakedGenericTypeReference(context, original, parameter)
                .withMutability(original.mutability)
                .withCombinedNullability(original.nullability)
        }
    }
}

private class NakedGenericTypeReference(
    override val context: CTContext,
    override val original: TypeReference,
    override val parameter: BoundTypeParameter,
) : GenericTypeReference() {
    override val effectiveBound: ResolvedTypeReference
        get() = parameter.bound
}

private class ResolvedBoundGenericTypeReference(
    override val context: CTContext,
    override val original: TypeReference,
    override val parameter: BoundTypeParameter,
    override val effectiveBound: ResolvedTypeReference,
) : GenericTypeReference()

private class MappedEffectiveBoundGenericTypeReference(
    private val delegate: GenericTypeReference,
    private val mapper: (ResolvedTypeReference) -> ResolvedTypeReference,
) : GenericTypeReference() {
    override val context = delegate.context
    override val original = delegate.original
    override val parameter = delegate.parameter
    override val effectiveBound by lazy {
        mapper(delegate.effectiveBound)
    }
}
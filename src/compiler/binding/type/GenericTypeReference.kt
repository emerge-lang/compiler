package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.andThen
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
        return effectiveBound.validate(forUsage) + setOfNotNull(forUsage.validateForTypeVariance(parameter.variance))
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return other is GenericTypeReference && this.parameter === other.parameter
    }

    override fun unify(assigneeType: ResolvedTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        return when (assigneeType) {
            is UnresolvedType -> unify(assigneeType.standInType, assignmentLocation, carry)
            is RootResolvedTypeReference -> carry.plusReporting(Reporting.valueNotAssignable(
                this,
                assigneeType,
                "the value of type parameter ${this.parameter.name} is not known at this point, cannot assign to references of type $simpleName",
                assignmentLocation,
            ))
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            is BoundTypeArgument -> TODO("What do do here? carry.plusLeft(simpleName, assigneeType) ?")
            is GenericTypeReference -> {
                // current assumption: confusing two distinct generics with the same name is not possible, given
                // that it is forbidden to shadow type variables (e.g. class A<T> { fun foo<T>() {} })
                // TODO: generic type inheritance, e.g. <A, B : A> and assigning a B to an A
                if (assigneeType.parameter == this.parameter) {
                    return carry
                } else {
                    return carry.plusReporting(Reporting.valueNotAssignable(
                        this,
                        assigneeType,
                        "The values of type parameters cannot possibly be known, so this assignment cannot be proven to be valid in all cases.",
                        assignmentLocation,
                    ))
                }
            }
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.defaultMutabilityTo(mutability) }
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        val selfEffective = when(parameter.variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> effectiveBound
            TypeVariance.IN -> BuiltinNothing.baseReference(context)
        }

        return when (other) {
            is RootResolvedTypeReference -> selfEffective.closestCommonSupertypeWith(other)
            is GenericTypeReference -> selfEffective.closestCommonSupertypeWith(other)
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is TypeVariable -> TODO()
            is UnresolvedType -> selfEffective.closestCommonSupertypeWith(other.standInType)
        }
    }

    override fun contextualize(context: TypeUnification): ResolvedTypeReference {
        return this
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): ResolvedTypeReference {
        if (this.parameter in variables) {
            return TypeVariable(this)
        }

        return this
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

private class MappedEffectiveBoundGenericTypeReference private constructor(
    private val delegate: GenericTypeReference,
    private val mapper: (ResolvedTypeReference) -> ResolvedTypeReference,
) : GenericTypeReference() {
    override val context = delegate.context
    override val original = delegate.original
    override val parameter = delegate.parameter
    override val effectiveBound by lazy {
        mapper(delegate.effectiveBound)
    }

    companion object {
        operator fun invoke(delegate: GenericTypeReference, mapper: (ResolvedTypeReference) -> ResolvedTypeReference): MappedEffectiveBoundGenericTypeReference {
            if (delegate is MappedEffectiveBoundGenericTypeReference) {
                return MappedEffectiveBoundGenericTypeReference(
                    delegate.delegate,
                    delegate.mapper andThen mapper
                )
            } else {
                return MappedEffectiveBoundGenericTypeReference(
                    delegate,
                    mapper,
                )
            }
        }
    }
}
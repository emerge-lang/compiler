package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.andThen
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

sealed class GenericTypeReference : BoundTypeReference {
    abstract val original: TypeReference
    abstract val parameter: BoundTypeParameter
    abstract val effectiveBound: BoundTypeReference

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

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return other is GenericTypeReference && this.parameter === other.parameter
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        return when (assigneeType) {
            is UnresolvedType -> unify(assigneeType.standInType, assignmentLocation, carry)
            is RootResolvedTypeReference -> carry.plusReporting(Reporting.valueNotAssignable(
                this,
                assigneeType,
                "$assigneeType cannot be proven to be a subtype of $simpleName",
                assignmentLocation,
            ))
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            is BoundTypeArgument -> when (assigneeType.variance) {
                TypeVariance.OUT,
                TypeVariance.UNSPECIFIED -> unify(assigneeType.type, assignmentLocation, carry)
                TypeVariance.IN -> unify(BoundTypeParameter.TYPE_PARAMETER_DEFAULT_BOUND, assignmentLocation, carry)
            }
            is GenericTypeReference -> {
                // current assumption: confusing two distinct generics with the same name is not possible, given
                // that it is forbidden to shadow type variables (e.g. class A<T> { fun foo<T>() {} })
                if (assigneeType.isSubtypeOf(this)) {
                    return carry
                } else {
                    return carry.plusReporting(Reporting.valueNotAssignable(
                        this,
                        assigneeType,
                        "${assigneeType.simpleName} cannot be proven to be a subtype of $simpleName",
                        assignmentLocation,
                    ))
                }
            }
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.defaultMutabilityTo(mutability) }
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (other) {
            is RootResolvedTypeReference,
            is UnresolvedType-> effectiveBound.closestCommonSupertypeWith(other)
            is GenericTypeReference -> {
                if (this.isSubtypeOf(other)) {
                    other
                } else if (other.isSubtypeOf(this)) {
                    this
                } else {
                    effectiveBound.closestCommonSupertypeWith(other.effectiveBound)
                }
            }
            is BoundTypeArgument -> other.closestCommonSupertypeWith(this)
            is TypeVariable -> throw InternalCompilerError("not implemented as it was assumed that this can never happen")
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return this
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        // TODO: this linear search is super inefficient, optimize
        val binding = context.bindings.entries.find { it.key.parameter == this.parameter }
        return binding?.value ?: this
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeReference {
        if (this.parameter in variables) {
            return TypeVariable(this)
        }

        return this
    }

    private fun isSubtypeOf(other: GenericTypeReference): Boolean {
        if (this.parameter == other.parameter) {
            return true
        }

        val bound = this.effectiveBound
        if (bound !is GenericTypeReference){
            return false
        }

        return bound.isSubtypeOf(other)
    }

    private fun mapEffectiveBound(mapper: (BoundTypeReference) -> BoundTypeReference): MappedEffectiveBoundGenericTypeReference {
        return MappedEffectiveBoundGenericTypeReference(this, mapper)
    }

    override fun toBackendIr(): IrType = IrGenericTypeReferenceImpl(
        parameter.toBackendIr(),
        effectiveBound.toBackendIr(),
    )

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
        operator fun invoke(original: TypeReference, parameter: BoundTypeParameter): GenericTypeReference {
            return NakedGenericTypeReference(original, parameter)
                .withMutability(original.mutability)
                .withCombinedNullability(original.nullability)
        }
    }
}

private class NakedGenericTypeReference(
    override val original: TypeReference,
    override val parameter: BoundTypeParameter,
) : GenericTypeReference() {
    override val effectiveBound: BoundTypeReference
        get() = parameter.bound
}

private class ResolvedBoundGenericTypeReference(
    override val original: TypeReference,
    override val parameter: BoundTypeParameter,
    override val effectiveBound: BoundTypeReference,
) : GenericTypeReference()

private class MappedEffectiveBoundGenericTypeReference private constructor(
    private val delegate: GenericTypeReference,
    private val mapper: (BoundTypeReference) -> BoundTypeReference,
) : GenericTypeReference() {
    override val original = delegate.original
    override val parameter = delegate.parameter
    override val effectiveBound by lazy {
        mapper(delegate.effectiveBound)
    }

    companion object {
        operator fun invoke(delegate: GenericTypeReference, mapper: (BoundTypeReference) -> BoundTypeReference): MappedEffectiveBoundGenericTypeReference {
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

private class IrGenericTypeReferenceImpl(
    override val parameter: IrBaseType.Parameter,
    override val effectiveBound: IrType,
) : IrGenericTypeReference {
    override fun toString() = "IrGenericReference[${parameter.name} : $effectiveBound]"
}
package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span
import compiler.util.andThen
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.independentToString

sealed class GenericTypeReference : BoundTypeReference {
    abstract val original: NamedTypeReference
    abstract val parameter: BoundTypeParameter
    abstract val effectiveBound: BoundTypeReference

    override val simpleName get() = parameter.name
    override val isNullable get() = effectiveBound.isNullable
    override val mutability: TypeMutability get() {
        val givenMutability = original.mutability
        if (givenMutability == null || !givenMutability.isAssignableTo(effectiveBound.mutability)) {
            return effectiveBound.mutability
        }
        return givenMutability
    }
    override val baseTypeOfLowerBound get()= effectiveBound.baseTypeOfLowerBound
    override val span get() = original.span
    override val inherentTypeBindings = TypeUnification.EMPTY
    override val isNonNullableNothing get() = effectiveBound.isNonNullableNothing
    override val isPartiallyUnresolved get() = effectiveBound.isPartiallyUnresolved

    override fun withMutability(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.withMutability(mutability) }
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.withMutabilityUnionedWith(mutability) }
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): GenericTypeReference {
        return mapEffectiveBound { it.withMutabilityLimitedTo(limitToMutability) }
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return when(nullability) {
            TypeReference.Nullability.UNSPECIFIED -> this
            TypeReference.Nullability.NULLABLE -> NullableTypeReference(this)
            TypeReference.Nullability.NOT_NULLABLE -> mapEffectiveBound { it.withCombinedNullability(nullability) }
        }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        effectiveBound.validate(forUsage, diagnosis)
        forUsage.validateForTypeVariance(parameter.variance, diagnosis)
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return when (other) {
            is GenericTypeReference -> this.parameter === other.parameter
            is NullableTypeReference -> hasSameBaseTypeAs(other.nested)
            else -> false
        }
    }

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return effectiveBound.findMemberFunction(name)
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> {
        return effectiveBound.findMemberVariable(name)
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        return when (assigneeType) {
            is NullableTypeReference -> {
                // TODO: try the assignment ignoring the nullability problem. If it works, report the nullability problem
                // otherwise, report the bigger/harder to fix problem first. This requires code in TypeUnification
                // that can determine success/failure of a sub-unification
                carry.plusDiagnostic(ValueNotAssignableDiagnostic(this, assigneeType, "Cannot assign a possibly null value to a non-nullable reference", assignmentLocation))
            }
            is ErroneousType -> unify(assigneeType.asNothing, assignmentLocation, carry)
            is RootResolvedTypeReference -> {
                if (assigneeType.isNonNullableNothing) carry else carry.plusDiagnostic(ValueNotAssignableDiagnostic(
                    this,
                    assigneeType,
                    "$assigneeType cannot be proven to be a subtype of $this",
                    assignmentLocation,
                ))
            }
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            is BoundTypeArgument -> when (assigneeType.variance) {
                TypeVariance.OUT,
                TypeVariance.UNSPECIFIED -> unify(assigneeType.type, assignmentLocation, carry)
                TypeVariance.IN -> unify(context.swCtx.getTopType(span ?: Span.UNKNOWN), assignmentLocation, carry)
            }
            is GenericTypeReference -> {
                // current assumption: confusing two distinct generics with the same name is not possible, given
                // that it is forbidden to shadow type variables (e.g. class A<T> { fun foo<T>() {} })
                if (assigneeType.isSubtypeOf(this)) {
                    return carry
                } else {
                    return carry.plusDiagnostic(ValueNotAssignableDiagnostic(
                        this,
                        assigneeType,
                        "$assigneeType cannot be proven to be a subtype of $this",
                        assignmentLocation,
                    ))
                }
            }
            is BoundIntersectionTypeReference -> {
                return assigneeType.flippedUnify(
                    this,
                    assignmentLocation,
                    carry,
                    reason = { "$assigneeType cannot be proven to be a subtype of $this" },
                )
            }
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): GenericTypeReference {
        /*
        the mutability of a parameter-type is never known exactly in the generic code,
        hence there is no point in defaulting the mutability. E.g. this code:

        class SomeBox<T> {
            var value: T = init
        }

        in this case, the `var` allows the `value` member var to be reassigned. But that doesn't mean
        that the type of the member variable should me `mut T`. For `SomeBox<const Any>` that would even be
        nonsensical. This method being a noop correctly implements this special case.

        */
        return this
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (other) {
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
            is RootResolvedTypeReference -> {
                if (other.baseType == context.swCtx.nothing) {
                    return this
                }

                return effectiveBound.closestCommonSupertypeWith(other)
            }
            else -> effectiveBound.closestCommonSupertypeWith(other)
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return this
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        var instantiated = context.getFinalValueFor(this.parameter)
        if (original.mutability != null) {
            instantiated = instantiated.withMutabilityUnionedWith(this.mutability)
        }
        return instantiated.withCombinedNullability(original.nullability)
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        val withTypeVariableBound = mapEffectiveBound { it.withTypeVariables(variables) }

        if (this.parameter !in variables) {
            return withTypeVariableBound
        }

        return TypeVariable(withTypeVariableBound)
    }

    override fun asAstReference(): NamedTypeReference = original

    private fun isSubtypeOf(other: GenericTypeReference): Boolean {
        if (this.parameter == other.parameter) {
            return this.mutability.isAssignableTo(other.mutability)
        }

        val bound = this.effectiveBound
        if (bound !is GenericTypeReference) {
            return false
        }

        return bound.isSubtypeOf(other)
    }

    private fun mapEffectiveBound(mapper: (BoundTypeReference) -> BoundTypeReference): GenericTypeReference {
        return MappedEffectiveBoundGenericTypeReference(this, mapper)
    }

    override fun toBackendIr(): IrType = IrGenericTypeReferenceImpl(
        parameter.toBackendIr(),
        effectiveBound.toBackendIr(),
    )

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is GenericTypeReference) return false

        if (other.mutability != this.mutability) return false
        if (other.parameter != this.parameter) return false
        if (other.effectiveBound != this.effectiveBound) return false

        return true
    }

    override fun hashCode(): Int {
        var result = mutability.hashCode()
        result = 31 * result + parameter.hashCode()
        result = 31 * result + effectiveBound.hashCode()
        return result
    }

    override fun toString(): String {
        var str = ""

        if (original.mutability != null) {
            str += "${original.mutability} "
        } else if (mutability != parameter.bound.mutability) {
            str += "$mutability "
        }

        str += simpleName
        return str
    }

    companion object {
        operator fun invoke(original: NamedTypeReference, parameter: BoundTypeParameter): BoundTypeReference {
            return NakedGenericTypeReference(original, parameter)
                .withMutability(original.mutability)
                .withCombinedNullability(original.nullability)
        }
    }
}

private class NakedGenericTypeReference(
    override val original: NamedTypeReference,
    override val parameter: BoundTypeParameter,
) : GenericTypeReference() {
    override val context = parameter.context
    override val effectiveBound: BoundTypeReference
        get() = parameter.bound
}

private class MappedEffectiveBoundGenericTypeReference private constructor(
    private val delegate: GenericTypeReference,
    private val mapper: (BoundTypeReference) -> BoundTypeReference,
) : GenericTypeReference() {
    override val context = delegate.context
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

internal class IrGenericTypeReferenceImpl(
    override val parameter: IrBaseType.Parameter,
    override val effectiveBound: IrType,
) : IrGenericTypeReference {
    override fun toString() = independentToString()
    override fun asNullable(): IrGenericTypeReference = IrGenericTypeReferenceImpl(parameter, effectiveBound.asNullable())
}
package compiler.binding.type

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

class BoundTypeArgument(
    override val context: CTContext,
    val astNode: TypeArgument,
    val variance: TypeVariance,
    val type: BoundTypeReference,
) : BoundTypeReference {
    init {
        check(type !is BoundTypeArgument)
    }
    override val isNullable get() = type.isNullable
    override val mutability get() = type.mutability
    override val baseTypeOfLowerBound get()= type.baseTypeOfLowerBound
    override val simpleName get() = toString()
    override val span get() = astNode.span
    override val isNonNullableNothing get() = type.isNonNullableNothing

    override val inherentTypeBindings: TypeUnification
        get() = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        context,
        astNode,
        variance,
        type.defaultMutabilityTo(when (mutability) {
            TypeMutability.EXCLUSIVE -> TypeMutability.READONLY
            else -> mutability
        }),
    )

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        forUsage.validateForTypeVariance(variance, diagnosis)
        type.validate(forUsage.deriveIrrelevant(), diagnosis)
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeArgument {
        return BoundTypeArgument(context, astNode, variance, type.withTypeVariables(variables))
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        if (assigneeType !is BoundTypeArgument && this.variance == TypeVariance.OUT) {
            if (assigneeType.isNonNullableNothing) {
                return carry
            }

            return carry.plusDiagnostic(ValueNotAssignableDiagnostic(this, assigneeType, "Cannot assign to a reference of an out-variant type", assignmentLocation))
        }

        when (assigneeType) {
            is RootResolvedTypeReference,
            is NullableTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundTypeArgument -> {
                if (this.variance == TypeVariance.UNSPECIFIED) {
                    val carry2 = type.unify(assigneeType.type, assignmentLocation, carry)

                    if (assigneeType.variance != TypeVariance.UNSPECIFIED) {
                        return carry2.plusDiagnostic(ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign an in-variant value to an exact-variant reference", assignmentLocation))
                    }

                    // target needs to use the type in both IN and OUT fashion -> source must match exactly
                    val carry3 = this.type.unify(assigneeType.type, assignmentLocation, carry2)
                    return assigneeType.type.unify(this.type, assignmentLocation, carry3)
                }

                if (this.variance == TypeVariance.OUT) {
                    if (assigneeType.variance == TypeVariance.OUT || assigneeType.variance == TypeVariance.UNSPECIFIED) {
                        return this.type.unify(assigneeType.type, assignmentLocation, carry)
                    }

                    check(assigneeType.variance == TypeVariance.IN)
                    return carry.plusDiagnostic(
                        ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign in-variant value to out-variant reference", assignmentLocation)
                    )
                }

                check(this.variance == TypeVariance.IN)
                if (assigneeType.variance == TypeVariance.IN || assigneeType.variance == TypeVariance.UNSPECIFIED) {
                    // IN variance reverses the hierarchy direction
                    return assigneeType.type.unify(this.type, assignmentLocation, carry)
                }

                return carry.plusDiagnostic(
                    ValueNotAssignableDiagnostic(this, assigneeType, "cannot assign out-variant value to in-variant reference", assignmentLocation)
                )
            }
            is GenericTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundIntersectionTypeReference -> return assigneeType.flippedUnify(this, assignmentLocation, carry) {
                "$assigneeType is not a subtype of $this"
            }
            is UnresolvedType -> {
                return unify(assigneeType.standInType, assignmentLocation, carry)
            }
            is TypeVariable -> return assigneeType.flippedUnify(this, assignmentLocation, carry)
        }
    }

    /**
     * @see BoundTypeReference.instantiateFreeVariables
     */
    override fun instantiateFreeVariables(context: TypeUnification,): BoundTypeArgument {
        val binding = type.instantiateFreeVariables(context)
        if (binding is BoundTypeArgument) {
            return binding
        }

        return BoundTypeArgument(this.context, astNode, variance, binding)
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeArgument {
        var nestedInstantiated = type.instantiateAllParameters(context)
        var isNullable: Boolean
        if (nestedInstantiated is NullableTypeReference) {
            isNullable = true
            nestedInstantiated = nestedInstantiated.nested
        } else {
            isNullable = false
        }
        val resultVariance: TypeVariance
        if (nestedInstantiated is BoundTypeArgument) {
            if (nestedInstantiated.variance == TypeVariance.UNSPECIFIED || this.variance == TypeVariance.UNSPECIFIED) {
                resultVariance = nestedInstantiated.variance.takeUnless { it == TypeVariance.UNSPECIFIED } ?: variance
                nestedInstantiated = nestedInstantiated.type
            } else {
                resultVariance = TypeVariance.OUT
                nestedInstantiated = this.context.swCtx.topTypeRef.withMutability(this.mutability.intersect(nestedInstantiated.mutability))
                isNullable = this.isNullable || isNullable
            }
        } else {
            resultVariance = variance
        }

        if (isNullable) {
            nestedInstantiated = NullableTypeReference(nestedInstantiated)
        }

        return BoundTypeArgument(this.context, TypeArgument(resultVariance, nestedInstantiated.asAstReference()), resultVariance, nestedInstantiated)
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        if (type.mutability == mutability) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withMutability(mutability),
        )
    }

    override fun withMutabilityUnionedWith(mutability: TypeMutability?): BoundTypeReference {
        if (mutability == null || type.mutability == mutability) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withMutabilityUnionedWith(mutability),
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeArgument {
        val newMutability = type.mutability.limitedTo(limitToMutability)
        if (newMutability == type.mutability) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withMutabilityLimitedTo(limitToMutability)
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withCombinedNullability(nullability),
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> type.closestCommonSupertypeWith(other)
            TypeVariance.IN -> context.swCtx.any.baseReference.closestCommonSupertypeWith(other)
        }
    }

    /**
     * Like [closestCommonSupertypeWith], but also respects semantics specific to [BoundTypeArgument]. To be
     * used in [BoundTypeReference.closestCommonSupertypeWith] for parametric types.
     */
    fun intersect(other: BoundTypeArgument): BoundTypeArgument {
        if (this == other) {
            return this
        }

        val resultVariance = when {
            this.variance == TypeVariance.OUT || other.variance == TypeVariance.OUT -> TypeVariance.OUT
            this.variance == TypeVariance.IN || other.variance == TypeVariance.IN -> TypeVariance.IN
            else -> {
                check(this.variance == other.variance && this.variance == TypeVariance.UNSPECIFIED)
                TypeVariance.OUT
            }
        }

        val resultType = when (resultVariance) {
            TypeVariance.IN -> this.type.intersect(other.type)
            TypeVariance.OUT -> this.type.closestCommonSupertypeWith(other.type)
            TypeVariance.UNSPECIFIED -> error("should never happen, intellij realizes this but not kotlinc")
        }

        return BoundTypeArgument(
            this.context,
            TypeArgument(resultVariance, resultType.asAstReference()),
            resultVariance,
            resultType,
        )
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> {
        return type.findMemberVariable(name)
    }

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return type.findMemberFunction(name)
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return type.hasSameBaseTypeAs(other)
    }

    override fun asAstReference(): TypeReference {
        return type.asAstReference()
    }

    override fun toBackendIr(): IrType = type.toBackendIr()

    fun toBackendIrAsTypeArgument(): IrParameterizedType.Argument = IrTypeArgumentImpl(variance.backendIr, type.toBackendIr())

    override fun toString(): String {
        if (variance == TypeVariance.UNSPECIFIED) {
            return type.toString()
        }

        return "$variance $type"
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is BoundTypeArgument) return false

        if (variance != other.variance) return false
        if (type != other.type) return false

        return true
    }

    override fun hashCode(): Int {
        var result = variance.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }
}

private class IrTypeArgumentImpl(
    override val variance: IrTypeVariance,
    override val type: IrType
) : IrParameterizedType.Argument {
    override fun toString() = "${variance.name.lowercase()} $type"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IrTypeArgumentImpl) return false

        if (variance != other.variance) return false
        if (type != other.type) return false

        return true
    }

    override fun hashCode(): Int {
        var result = variance.hashCode()
        result = 31 * result + type.hashCode()
        return result
    }
}
package compiler.binding.type

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.lexer.Span
import compiler.reportings.Diagnosis
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

class BoundTypeArgument(
    val context: CTContext,
    val astNode: TypeArgument,
    val variance: TypeVariance,
    val type: BoundTypeReference,
) : BoundTypeReference {
    init {
        check(type !is BoundTypeArgument)
    }
    override val isNullable get()= type.isNullable
    override val mutability get() = type.mutability
    override val simpleName get() = toString()
    override val span get() = astNode.span

    override val inherentTypeBindings: TypeUnification
        get() = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        context,
        astNode,
        variance,
        type.defaultMutabilityTo(mutability),
    )

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        forUsage.validateForTypeVariance(variance, diagnosis)
        type.validate(forUsage.deriveIrrelevant(), diagnosis)
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeArgument {
        return BoundTypeArgument(context, astNode, variance, type.withTypeVariables(variables))
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        if (assigneeType !is BoundTypeArgument && this.variance == TypeVariance.OUT) {
            return carry.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "Cannot assign to a reference of an out-variant type", assignmentLocation))
        }

        if (this.type is TypeVariable) {
            return this.type.unify(assigneeType, assignmentLocation, carry)
        }

        when (assigneeType) {
            is RootResolvedTypeReference,
            is NullableTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundTypeArgument -> {
                if (type is TypeVariable || assigneeType.type is TypeVariable) {
                    return type.unify(assigneeType.type, assignmentLocation, carry)
                }

                if (this.variance == TypeVariance.UNSPECIFIED) {
                    val carry2 = type.unify(assigneeType.type, assignmentLocation, carry)

                    val assigneeActualTypeNotNullable = assigneeType.type.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)

                    // target needs to use the type in both IN and OUT fashion -> source must match exactly
                    if (assigneeActualTypeNotNullable !is GenericTypeReference && !assigneeActualTypeNotNullable.hasSameBaseTypeAs(this.type)) {
                        return carry2.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "the exact type ${this.type} is required", assignmentLocation))
                    }

                    if (assigneeType.variance != TypeVariance.UNSPECIFIED) {
                        return carry2.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "cannot assign an in-variant value to an exact-variant reference", assignmentLocation))
                    }

                    // checks for mutability and nullability
                    return this.type.unify(assigneeType.type, assignmentLocation, carry2)
                }

                if (this.variance == TypeVariance.OUT) {
                    if (assigneeType.variance == TypeVariance.OUT || assigneeType.variance == TypeVariance.UNSPECIFIED) {
                        return this.type.unify(assigneeType.type, assignmentLocation, carry)
                    }

                    check(assigneeType.variance == TypeVariance.IN)
                    return carry.plusReporting(
                        Reporting.valueNotAssignable(this, assigneeType, "cannot assign in-variant value to out-variant reference", assignmentLocation)
                    )
                }

                check(this.variance == TypeVariance.IN)
                if (assigneeType.variance == TypeVariance.IN || assigneeType.variance == TypeVariance.UNSPECIFIED) {
                    // IN variance reverses the hierarchy direction
                    return assigneeType.type.unify(this.type, assignmentLocation, carry)
                }

                return carry.plusReporting(
                    Reporting.valueNotAssignable(this, assigneeType, "cannot assign out-variant value to in-variant reference", assignmentLocation)
                )
            }
            is GenericTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
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
        val isNullable: Boolean
        if (nestedInstantiated is NullableTypeReference) {
            isNullable = true
            nestedInstantiated = nestedInstantiated.nested
        } else {
            isNullable = false
        }
        if (nestedInstantiated is BoundTypeArgument) {
            nestedInstantiated = nestedInstantiated.type
        }
        if (isNullable) {
            nestedInstantiated = NullableTypeReference(nestedInstantiated)
        }

        return BoundTypeArgument(this.context, astNode, variance, nestedInstantiated)
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        if (type.mutability == modifier) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withMutability(modifier),
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundTypeReference {
        if (mutability == null || type.mutability == mutability) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withCombinedMutability(mutability),
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

    override fun findMemberVariable(name: String): BoundBaseTypeMemberVariable? {
        return type.findMemberVariable(name)
    }

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return type.findMemberFunction(name)
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return type.hasSameBaseTypeAs(other)
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
package compiler.binding.type

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.SideEffectPrediction
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

class BoundTypeArgument(
    val context: CTContext,
    val argumentAstNode: TypeArgument,
    val variance: TypeVariance,
    val type: BoundTypeReference,
) : BoundTypeReference {
    init {
        check(type !is BoundTypeArgument)
    }
    override val isNullable get()= type.isNullable
    override val mutability get() = type.mutability
    override val span get() = argumentAstNode.span

    override val inherentTypeBindings: TypeUnification
        get() = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        context,
        argumentAstNode,
        variance,
        type.defaultMutabilityTo(mutability),
    )

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return setOfNotNull(forUsage.validateForTypeVariance(variance)) + type.validate(forUsage.deriveIrrelevant())
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeArgument {
        return BoundTypeArgument(context, argumentAstNode, variance, type.withTypeVariables(variables))
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
            is BoundFunctionType,
            is NullableTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundTypeArgument -> {
                return unifyTypeArguments(this.type, this.variance, assigneeType.type, assigneeType.variance, assignmentLocation, carry)
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

        return BoundTypeArgument(this.context, argumentAstNode, variance, binding)
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

        return BoundTypeArgument(this.context, argumentAstNode, variance, nestedInstantiated)
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        if (type.mutability == modifier) {
            return this
        }

        return BoundTypeArgument(
            context,
            argumentAstNode,
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
            argumentAstNode,
            variance,
            type.withCombinedMutability(mutability),
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return BoundTypeArgument(
            context,
            argumentAstNode,
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

    override val destructorThrowBehavior = SideEffectPrediction.POSSIBLY

    override fun toBackendIr(): IrType = type.toBackendIr()

    fun toBackendIrAsTypeArgument(): IrParameterizedType.Argument = IrTypeArgumentImpl(variance.backendIr, type.toBackendIr())

    override fun toString(): String {
        if (variance == TypeVariance.UNSPECIFIED) {
            return type.toString()
        }

        return "$variance $type"
    }

    companion object {
        fun unifyTypeArguments(
            targetArgType: BoundTypeReference,
            targetArgVariance: TypeVariance,
            assigneeArgType: BoundTypeReference,
            assigneeArgVariance: TypeVariance,
            assignmentLocation: Span,
            carry: TypeUnification,
        ): TypeUnification {
            if (targetArgType is TypeVariable || assigneeArgType is TypeVariable) {
                return targetArgType.unify(assigneeArgType, assignmentLocation, carry)
            }

            if (targetArgVariance == TypeVariance.UNSPECIFIED) {
                val carry2 = targetArgType.unify(assigneeArgType, assignmentLocation, carry)

                val assigneeActualTypeNotNullable = assigneeArgType.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)

                // target needs to use the type in both IN and OUT fashion -> source must match exactly
                if (assigneeActualTypeNotNullable !is GenericTypeReference && !assigneeActualTypeNotNullable.hasSameBaseTypeAs(targetArgType)) {
                    return carry2.plusReporting(Reporting.valueNotAssignable(targetArgType, assigneeArgType, "the exact type $targetArgType is required", assignmentLocation))
                }

                if (assigneeArgVariance != TypeVariance.UNSPECIFIED) {
                    return carry2.plusReporting(Reporting.valueNotAssignable(targetArgType, assigneeArgType, "cannot assign an in-variant value to an exact-variant reference", assignmentLocation))
                }

                // checks for mutability and nullability
                return targetArgType.unify(assigneeArgType, assignmentLocation, carry2)
            }

            if (targetArgVariance == TypeVariance.OUT) {
                if (assigneeArgVariance == TypeVariance.OUT || assigneeArgVariance == TypeVariance.UNSPECIFIED) {
                    return targetArgType.unify(assigneeArgType, assignmentLocation, carry)
                }

                check(assigneeArgVariance == TypeVariance.IN)
                return carry.plusReporting(
                    Reporting.valueNotAssignable(targetArgType, assigneeArgType, "cannot assign in-variant value to out-variant reference", assignmentLocation)
                )
            }

            check(targetArgVariance == TypeVariance.IN)
            if (assigneeArgVariance == TypeVariance.IN || assigneeArgVariance == TypeVariance.UNSPECIFIED) {
                // IN variance reverses the hierarchy direction
                return assigneeArgType.unify(targetArgType, assignmentLocation, carry)
            }

            return carry.plusReporting(
                Reporting.valueNotAssignable(targetArgType, assigneeArgType, "cannot assign out-variant value to in-variant reference", assignmentLocation)
            )
        }
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
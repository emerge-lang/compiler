package compiler.binding.type

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

class BoundTypeArgument(
    val astNode: TypeArgument,
    val variance: TypeVariance,
    val type: BoundTypeReference,
) : BoundTypeReference {
    override val isNullable get() = type.isNullable
    override val mutability get() = type.mutability
    override val simpleName get() = toString()
    override val sourceLocation get() = astNode.sourceLocation

    override val inherentTypeBindings: TypeUnification
        get() = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        astNode,
        variance,
        type.defaultMutabilityTo(mutability),
    )

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return setOfNotNull(forUsage.validateForTypeVariance(variance)) + type.validate(TypeUseSite.Irrelevant)
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeArgument {
        return BoundTypeArgument(astNode, variance, type.withTypeVariables(variables))
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        if (assigneeType !is BoundTypeArgument && this.variance == TypeVariance.OUT) {
            return carry.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "Cannot assign to a reference of an out-variant type", assignmentLocation))
        }

        if (this.type is TypeVariable) {
            return this.type.unify(assigneeType, assignmentLocation, carry)
        }

        when (assigneeType) {
            is RootResolvedTypeReference -> {
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundTypeArgument -> {
                if (assigneeType.type is TypeVariable) {
                    return type.unify(assigneeType.type, assignmentLocation, carry)
                }

                if (this.variance == TypeVariance.UNSPECIFIED) {
                    // target needs to use the type in both IN and OUT fashion -> source must match exactly
                    if (assigneeType.type !is GenericTypeReference && !assigneeType.type.hasSameBaseTypeAs(this.type)) {
                        return carry.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "the exact type ${this.type} is required", assignmentLocation))
                    }

                    if (assigneeType.variance != TypeVariance.UNSPECIFIED) {
                        return carry.plusReporting(Reporting.valueNotAssignable(this, assigneeType, "cannot assign an in-variant value to an exact-variant reference", assignmentLocation))
                    }

                    // checks for mutability and nullability
                    return this.type.unify(assigneeType.type, assignmentLocation, carry)
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

        return BoundTypeArgument(astNode, variance, binding)
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeArgument {
        return BoundTypeArgument(astNode, variance, type.instantiateAllParameters(context))
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        if (type.mutability == modifier) {
            return this
        }

        return BoundTypeArgument(
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
            astNode,
            variance,
            type.withCombinedMutability(mutability),
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return BoundTypeArgument(
            astNode,
            variance,
            type.withCombinedNullability(nullability),
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return when (variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> type.closestCommonSupertypeWith(other)
            TypeVariance.IN -> BuiltinAny.baseReference.closestCommonSupertypeWith(other)
        }
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
}

private class IrTypeArgumentImpl(
    override val variance: IrTypeVariance,
    override val type: IrType
) : IrParameterizedType.Argument {
    override fun toString() = "${variance.name.lowercase()} $type"
}
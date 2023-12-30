package compiler.binding.type

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class BoundTypeArgument(
    override val context: CTContext,
    val astNode: TypeArgument,
    val variance: TypeVariance,
    val type: ResolvedTypeReference,
) : ResolvedTypeReference {
    override val isNullable get() = type.isNullable
    override val mutability get() = type.mutability
    override val simpleName get() = toString()
    override val sourceLocation get() = astNode.sourceLocation

    override val inherentTypeBindings: TypeUnification
        get() = TypeUnification.EMPTY

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        context,
        astNode,
        variance,
        type.defaultMutabilityTo(mutability),
    )

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return setOfNotNull(forUsage.validateForTypeVariance(variance)) + type.validate(TypeUseSite.Irrelevant)
    }

    /**
     * @see ResolvedTypeReference.evaluateAssignabilityTo
     */
    override fun evaluateAssignabilityTo(target: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting? {
        val selfEffectiveType = when (variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> type
            TypeVariance.IN -> BuiltinAny.baseReference(this.context)
        }

        when (target) {
            is RootResolvedTypeReference -> return selfEffectiveType.evaluateAssignabilityTo(target, assignmentLocation)
            is GenericTypeReference -> return selfEffectiveType.evaluateAssignabilityTo(target, assignmentLocation)
            is UnresolvedType -> return selfEffectiveType.evaluateAssignabilityTo(target.standInType, assignmentLocation)
            is BoundTypeArgument -> {
                if (target.variance == TypeVariance.UNSPECIFIED) {
                    // target needs to use the type in both IN and OUT fashion -> source must match exactly
                    if (!this.type.hasSameBaseTypeAs(target.type)) {
                        return Reporting.valueNotAssignable(target, this, "the exact type ${target.type} is required", assignmentLocation)
                    }

                    if (this.variance != TypeVariance.UNSPECIFIED) {
                        return Reporting.valueNotAssignable(target, this, "cannot assign an in-variant value to an exact-variant reference", assignmentLocation)
                    }

                    // checks for mutability and nullability
                    return this.type.evaluateAssignabilityTo(target.type, assignmentLocation)
                }

                if (target.variance == TypeVariance.OUT) {
                    if (this.variance == TypeVariance.OUT || this.variance == TypeVariance.UNSPECIFIED) {
                        return this.type.evaluateAssignabilityTo(target.type, assignmentLocation)
                    }

                    assert(this.variance == TypeVariance.IN)
                    return Reporting.valueNotAssignable(target, this, "cannot assign in-variant value to out-variant reference", assignmentLocation)
                }

                assert(target.variance == TypeVariance.IN)
                if (this.variance == TypeVariance.IN || this.variance == TypeVariance.UNSPECIFIED) {
                    // IN variance reverses the hierarchy direction
                    return target.type.evaluateAssignabilityTo(this.type, assignmentLocation)
                }

                return Reporting.valueNotAssignable(target, this, "cannot assign out-variant value to in-variant reference", assignmentLocation)
            }
        }
    }

    override fun unify(assigneeType: ResolvedTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        when (assigneeType) {
            is RootResolvedTypeReference -> {
                // TODO: is variance important here?
                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is BoundTypeArgument -> {
                this.evaluateAssignabilityTo(assigneeType, sourceLocation ?: assigneeType.sourceLocation ?: SourceLocation.UNKNOWN)?.let {
                    return carry.plusReporting(it)
                }

                return type.unify(assigneeType, assignmentLocation, carry)
            }
            is GenericTypeReference -> {
                return carry.plusRight(assigneeType.simpleName, this)
            }
            is UnresolvedType -> {
                return unify(assigneeType.standInType, assignmentLocation, carry)
            }
        }
    }

    /**
     * @see ResolvedTypeReference.contextualize
     */
    override fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, ResolvedTypeReference>): BoundTypeArgument {
        return BoundTypeArgument(this.context, astNode, variance, type.contextualize(context, side))
    }

    override fun withMutability(modifier: TypeMutability?): ResolvedTypeReference {
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

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
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

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.withCombinedNullability(nullability),
        )
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        return when (variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> type.closestCommonSupertypeWith(other)
            TypeVariance.IN -> BuiltinAny.baseReference(context).closestCommonSupertypeWith(other)
        }
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return type.hasSameBaseTypeAs(other)
    }

    override fun toString(): String {
        if (variance == TypeVariance.UNSPECIFIED) {
            return type.toString()
        }

        return "$variance $type"
    }
}

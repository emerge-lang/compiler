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
    val astNode: TypeArgument?,
    val variance: TypeVariance,
    val type: ResolvedTypeReference,
) : ResolvedTypeReference {
    override val isNullable get() = type.isNullable
    override val mutability get() = type.mutability
    override val simpleName get() = toString()
    override val sourceLocation get() = astNode?.sourceLocation

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
    override fun evaluateAssignabilityTo(target: ResolvedTypeReference, assignmentSourceLocation: SourceLocation): ValueNotAssignableReporting? {
        val selfEffectiveType = when (variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> type
            TypeVariance.IN -> Any.baseReference(this.context)
        }

        when (target) {
            is RootResolvedTypeReference -> return selfEffectiveType.evaluateAssignabilityTo(target, assignmentSourceLocation)
            is GenericTypeReference -> return selfEffectiveType.evaluateAssignabilityTo(target, assignmentSourceLocation)
            is UnresolvedType -> return selfEffectiveType.evaluateAssignabilityTo(target.standInType, assignmentSourceLocation)
            is BoundTypeArgument -> {
                if (target.variance == TypeVariance.UNSPECIFIED) {
                    // target needs to use the type in both IN and OUT fashion -> source must match exactly
                    if (!this.type.hasSameBaseTypeAs(target.type)) {
                        return Reporting.valueNotAssignable(target, this, "the exact type ${target.type} is required", assignmentSourceLocation)
                    }

                    if (this.variance != TypeVariance.UNSPECIFIED) {
                        return Reporting.valueNotAssignable(target, this, "cannot assign an in-variant value to an exact-variant reference", assignmentSourceLocation)
                    }

                    // checks for mutability and nullability
                    return this.type.evaluateAssignabilityTo(target.type, assignmentSourceLocation)
                }

                if (target.variance == TypeVariance.OUT) {
                    if (this.variance == TypeVariance.OUT || this.variance == TypeVariance.UNSPECIFIED) {
                        return this.type.evaluateAssignabilityTo(target.type, assignmentSourceLocation)
                    }

                    assert(this.variance == TypeVariance.IN)
                    return Reporting.valueNotAssignable(target, this, "cannot assign in-variant value to out-variant reference", assignmentSourceLocation)
                }

                assert(target.variance == TypeVariance.IN)
                if (this.variance == TypeVariance.IN || this.variance == TypeVariance.UNSPECIFIED) {
                    // IN variance reverses the hierarchy direction
                    return target.type.evaluateAssignabilityTo(this.type, assignmentSourceLocation)
                }

                return Reporting.valueNotAssignable(target, this, "cannot assign out-variant value to in-variant reference", assignmentSourceLocation)
            }
        }
    }

    /**
     * @see ResolvedTypeReference.unify
     */
    override fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification {
        when (other) {
            is RootResolvedTypeReference -> {
                if (variance != TypeVariance.UNSPECIFIED) {
                    throw TypesNotUnifiableException(this, other, "Cannot unify concrete type with variant-type")
                }

                return type.unify(other, carry)
            }
            is BoundTypeArgument -> {
                // TODO: get source location?
                this.evaluateAssignabilityTo(other, SourceLocation.UNKNOWN)?.let {
                    throw TypesNotUnifiableException(this, other, it.reason)
                }

                return type.unify(other, carry)
            }
            is GenericTypeReference -> {
                return carry.plusRight(other.simpleName, this)
            }
            is UnresolvedType -> {
                return unify(other.standInType, carry)
            }
        }
    }

    /**
     * @see ResolvedTypeReference.contextualize
     */
    override fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, BoundTypeArgument>): BoundTypeArgument {
        return BoundTypeArgument(this.context, astNode, variance, type.contextualize(context, side))
    }

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        if (type.mutability == modifier) {
            return this
        }

        return BoundTypeArgument(
            context,
            astNode,
            variance,
            type.modifiedWith(modifier),
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
            TypeVariance.IN -> Any.baseReference(context).closestCommonSupertypeWith(other)
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

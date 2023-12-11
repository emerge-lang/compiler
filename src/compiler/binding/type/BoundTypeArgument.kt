package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class BoundTypeArgument(
    val variance: TypeVariance,
    val type: ResolvedTypeReference,
) {
    fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeArgument = BoundTypeArgument(
        variance,
        type.defaultMutabilityTo(mutability),
    )

    fun validate(): Collection<Reporting> {
        return type.validate()
    }

    /**
     * @see ResolvedTypeReference.evaluateAssignabilityTo
     */
    fun evaluateAssignabilityTo(target: BoundTypeArgument, assignmentSourceLocation: SourceLocation): ValueNotAssignableReporting? {
        if (target.variance == TypeVariance.UNSPECIFIED) {
            // target needs to use the type in both IN and OUT fashion -> source must match exactly
            if (!this.type.hasSameBaseTypeAs(target.type)) {
                // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
                return Reporting.valueNotAssignable(target.type, this.type, "the exact type ${target.type} is required", assignmentSourceLocation)
            }

            if (this.variance != TypeVariance.UNSPECIFIED) {
                // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
                return Reporting.valueNotAssignable(target.type, this.type, "cannot assign an in-variant value to an exact-variant reference", assignmentSourceLocation)
            }

            // checks for mutability and nullability
            return this.type.evaluateAssignabilityTo(target.type, assignmentSourceLocation)
        }

        if (target.variance == TypeVariance.OUT) {
            if (this.variance == TypeVariance.OUT || this.variance == TypeVariance.UNSPECIFIED) {
                return this.type.evaluateAssignabilityTo(target.type, assignmentSourceLocation)
            }

            assert(this.variance == TypeVariance.IN)
            // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
            return Reporting.valueNotAssignable(target.type, this.type, "cannot assign in-variant value to out-variant reference", assignmentSourceLocation)
        }

        assert(target.variance == TypeVariance.IN)
        if (this.variance == TypeVariance.IN || this.variance == TypeVariance.UNSPECIFIED) {
            // IN variance reverses the hierarchy direction
            return target.type.evaluateAssignabilityTo(this.type, assignmentSourceLocation)
        }

        // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
        return Reporting.valueNotAssignable(target.type, this.type, "cannot assign out-variant value to in-variant reference", assignmentSourceLocation)
    }

    /**
     * @see ResolvedTypeReference.unify
     */
    fun unify(other: BoundTypeArgument, carry: TypeUnification): TypeUnification {
        // TODO: get source location?
        // TODO: pass type with variance to reporting? probably when BoundTypeArgument : ResolvedTypeReference
        this.evaluateAssignabilityTo(other, SourceLocation.UNKNOWN)?.let {
            throw TypesNotUnifiableException(this.type, other.type, it.reason)
        }

        return type.unify(other.type, carry)
    }

    /**
     * @see ResolvedTypeReference.contextualize
     */
    fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, BoundTypeArgument>): BoundTypeArgument {
        return BoundTypeArgument(variance, type.contextualize(context, side))
    }

    override fun toString(): String {
        if (variance == TypeVariance.UNSPECIFIED) {
            return type.toString()
        }

        return "${variance.name.lowercase()} $type"
    }
}

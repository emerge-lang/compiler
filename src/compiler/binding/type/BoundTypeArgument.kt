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

    fun evaluateAssignabilityTo(target: BoundTypeArgument, assignmentSourceLocation: SourceLocation): ValueNotAssignableReporting? {
        if (target.variance == TypeVariance.UNSPECIFIED) {
            // target needs to use the type in both IN and OUT fashion -> source must match exactly
            if (!this.type.hasSameBaseTypeAs(target.type)) {
                // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
                return Reporting.valueNotAssignable(target.type, this.type, "The exact type ${target.type} is required", assignmentSourceLocation)
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
            return Reporting.valueNotAssignable(target.type, this.type, "Cannot assign in-variant value to out-variant reference", assignmentSourceLocation)
        }

        assert(target.variance == TypeVariance.IN)
        if (this.variance == TypeVariance.IN || this.variance == TypeVariance.UNSPECIFIED) {
            // IN variance reverses the hierarchy direction
            return target.type.evaluateAssignabilityTo(this.type, assignmentSourceLocation)
        }

        // TODO: can we pass target and this with variance? probably when BoundTypeArgument : ResolvedTypeReference
        return Reporting.valueNotAssignable(target.type, this.type, "Cannot assign out-variant value to in-variant reference", assignmentSourceLocation)
    }

    override fun toString(): String {
        if (variance == TypeVariance.UNSPECIFIED) {
            return type.toString()
        }

        return "${variance.name.lowercase()} $type"
    }
}

val s: Array<in Any> = TODO()

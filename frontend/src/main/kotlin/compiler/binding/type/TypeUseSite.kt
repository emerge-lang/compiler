package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.DefinitionWithVisibility
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.UnsupportedTypeUsageVarianceReporting

/**
 * Describes the [TypeVariance] of the usage side. E.g. function parameters are [TypeVariance.IN],
 * read-only properties are [TypeVariance.OUT], mutable properties are [TypeVariance.UNSPECIFIED].
 */
sealed class TypeUseSite(
    givenUsageLocation: SourceLocation?,
    val varianceDescription: String,
    val exposedBy: DefinitionWithVisibility?,
) {
    val usageLocation: SourceLocation = givenUsageLocation ?: SourceLocation.UNKNOWN

    abstract fun validateForTypeVariance(typeVariance: TypeVariance): Reporting?

    fun deriveIrrelevant(): Irrelevant = Irrelevant(usageLocation, exposedBy)

    // equals + hashCode are final because if the same location had
    // two different variances, something would be CLEARLY wrong

    final override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeUseSite) return false

        if (usageLocation != other.usageLocation) return false

        return true
    }

    final override fun hashCode(): Int {
        return usageLocation.hashCode()
    }


    class InUsage(
        usageLocation: SourceLocation?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "in", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance): UnsupportedTypeUsageVarianceReporting? {
            if (typeVariance != TypeVariance.IN && typeVariance != TypeVariance.UNSPECIFIED) {
                return Reporting.unsupportedTypeUsageVariance(this, typeVariance)
            }

            return null
        }
    }

    class OutUsage(
        usageLocation: SourceLocation?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "out", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance): UnsupportedTypeUsageVarianceReporting? {
            if (typeVariance != TypeVariance.OUT && typeVariance != TypeVariance.UNSPECIFIED) {
                return Reporting.unsupportedTypeUsageVariance(this, typeVariance)
            }

            return null
        }
    }

    class InvariantUsage(
        usageLocation: SourceLocation?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "invariant", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance): UnsupportedTypeUsageVarianceReporting? {
            if (typeVariance != TypeVariance.UNSPECIFIED) {
                return Reporting.unsupportedTypeUsageVariance(this, typeVariance)
            }

            return null
        }
    }

    class Irrelevant(
        usageLocation: SourceLocation?,
        exposedBy: DefinitionWithVisibility?,
    ) : TypeUseSite(usageLocation, "irrelevant", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance) = null
    }
}
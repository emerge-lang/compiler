package compiler.binding.type

import compiler.ast.type.TypeVariance
import compiler.binding.DefinitionWithVisibility
import compiler.lexer.Span
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.unsupportedTypeUsageVariance

/**
 * Describes the [TypeVariance] of the usage side. E.g. function parameters are [TypeVariance.IN],
 * read-only properties are [TypeVariance.OUT], mutable properties are [TypeVariance.UNSPECIFIED].
 */
sealed class TypeUseSite(
    givenUsageLocation: Span?,
    val varianceDescription: String,
    val exposedBy: DefinitionWithVisibility?,
) {
    val usageLocation: Span = givenUsageLocation ?: Span.UNKNOWN

    abstract fun validateForTypeVariance(typeVariance: TypeVariance, diagnosis: Diagnosis)

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
        usageLocation: Span?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "in", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance, diagnosis: Diagnosis) {
            if (typeVariance != TypeVariance.IN && typeVariance != TypeVariance.UNSPECIFIED) {
                diagnosis.unsupportedTypeUsageVariance(this, typeVariance)
            }
        }
    }

    class OutUsage(
        usageLocation: Span?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "out", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance, diagnosis: Diagnosis) {
            if (typeVariance != TypeVariance.OUT && typeVariance != TypeVariance.UNSPECIFIED) {
                diagnosis.unsupportedTypeUsageVariance(this, typeVariance)
            }
        }
    }

    class InvariantUsage(
        usageLocation: Span?,
        exposedBy: DefinitionWithVisibility?,
    ): TypeUseSite(usageLocation, "invariant", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance, diagnosis: Diagnosis) {
            if (typeVariance != TypeVariance.UNSPECIFIED) {
                diagnosis.unsupportedTypeUsageVariance(this, typeVariance)
            }
        }
    }

    class Irrelevant(
        usageLocation: Span?,
        exposedBy: DefinitionWithVisibility?,
    ) : TypeUseSite(usageLocation, "irrelevant", exposedBy) {
        override fun validateForTypeVariance(typeVariance: TypeVariance, diagnosis: Diagnosis) = Unit
    }
}
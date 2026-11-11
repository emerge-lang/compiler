package compiler.binding.expression

import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.SoftwareContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.isReadInAllInstantiations
import compiler.lexer.Span

/**
 * Describes how the evaluation result of an [BoundExpression] is used, e.g. "stored into a local variable",
 * "passed to function XYZ ..."
 */
interface ValueUsage {
    /**
     * the type with which the using side refers to the value. Can be `null` if the type cannot be statically
     * determined.
     */
    val usedAsType: BoundTypeReference?

    val usedWithMutability: TypeMutability get() = usedAsType?.mutability ?: TypeMutability.READONLY

    /**
     * Whether the using side refers to the value through a `read` reference for certain. It doesn't if [usedAsType]
     * is a type parameter, as that can be bound to a type of any mutability.
     */
    val isUsedAsReadReference: Boolean get() = usedAsType?.isReadInAllInstantiations() ?: true

    /**
     * [usedWithMutability], for deciding which other references may exist at the same time
     * ([TypeMutability.mayBeAliasedWith]): a reference of a type parameter can turn out to be `mut` or `const`, so it
     * is as demanding as an `exclusive` one, which only tolerates `read` references.
     */
    val usedWithMutabilityForAliasing: TypeMutability get() {
        val mutability = usedWithMutability
        return if (mutability == TypeMutability.READONLY && !isUsedAsReadReference) TypeMutability.EXCLUSIVE else mutability
    }

    /**
     * ownership semantics of how the value is used. E.g. assigning to an object member definitely is
     * [VariableOwnership.CAPTURED].
     */
    val usageOwnership: VariableOwnership

    /**
     * Where the usage happens
     */
    val span: Span

    /**
     * @return a [ValueUsage] identical to `this`, except that [usedAsType] has been transformed using [mapper].
     */
    fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage

    fun describeForDiagnostic(descriptionOfUsedValue: String): String

    companion object {
        fun deriveFromAndThen(
            deriveUsingType: BoundTypeReference?,
            deriveWithOwnership: VariableOwnership,
            andThen: ValueUsage
        ): ValueUsage {
            return if (andThen is DeriveFromAndThenValueUsage) {
                if (andThen.usedAsType == deriveUsingType && andThen.usageOwnership == deriveWithOwnership) {
                    andThen
                } else {
                    DeriveFromAndThenValueUsage(andThen.andThenUsage, deriveUsingType, deriveWithOwnership)
                }
            } else {
                DeriveFromAndThenValueUsage(andThen, deriveUsingType, deriveWithOwnership)
            }
        }
    }
}

data class CreateReferenceValueUsage(
    override val usedAsType: BoundTypeReference?,
    val referenceCreatedAt: Span,
    override val usageOwnership: VariableOwnership,
) : ValueUsage {
    override val span = referenceCreatedAt

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }
        return copy(usedAsType = mapper(usedAsType))
    }

    override fun describeForDiagnostic(descriptionOfUsedValue: String): String {
        val mutabilityPart = when (val it = usedAsType?.mutability?.toString()) {
            null -> ""
            else -> "$it "
        }
        return "creating a ${mutabilityPart}reference to $descriptionOfUsedValue"
    }
}

class ReturnValueFromFunctionUsage(
    returnAsType: BoundTypeReference?,
    returnActionAt: Span,
) : ValueUsage {
    override val usedAsType = returnAsType
    override val usageOwnership = VariableOwnership.CAPTURED
    override val span = returnActionAt
    override fun describeForDiagnostic(descriptionOfUsedValue: String): String {
        return "returning $descriptionOfUsedValue"
    }

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return ReturnValueFromFunctionUsage(mapper(usedAsType), span)
    }
}

class ThrowValueUsage(
    thrownAsType: BoundTypeReference?,
    thrownAt: Span,
) : ValueUsage {
    override val usedAsType = thrownAsType
    override val usageOwnership = VariableOwnership.CAPTURED
    override val span = thrownAt
    override fun describeForDiagnostic(descriptionOfUsedValue: String): String {
        return "throwing $descriptionOfUsedValue"
    }

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return ThrowValueUsage(mapper(usedAsType), span)
    }
}

class MixinValueUsage(
    mixedInAsType: BoundTypeReference?,
    mixedInAt: Span,
) : ValueUsage {
    override val usedAsType = mixedInAsType
    override val span = mixedInAt
    override val usageOwnership = VariableOwnership.CAPTURED
    override fun describeForDiagnostic(descriptionOfUsedValue: String): String {
        return "mixing in $descriptionOfUsedValue"
    }

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return MixinValueUsage(mapper(usedAsType), span)
    }
}

class TypeCheckValueUsage private constructor(
    override val usedAsType: BoundTypeReference,
    override val span: Span,
) : ValueUsage {
    constructor(softwareContext: SoftwareContext, span: Span) : this(
        softwareContext.any.getBoundReferenceAssertNoTypeParameters(span)
            .withMutability(TypeMutability.READONLY)
            .withCombinedNullability(TypeReference.Nullability.NULLABLE),
        span,
    )

    override val usageOwnership = VariableOwnership.BORROWED

    override fun describeForDiagnostic(descriptionOfUsedValue: String) = "reflecting the type of $descriptionOfUsedValue"

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        return TypeCheckValueUsage(mapper(usedAsType), span)
    }
}

data class DeriveFromAndThenValueUsage(
    val andThenUsage: ValueUsage,
    override val usedAsType: BoundTypeReference?,
    override val usageOwnership: VariableOwnership,
) : ValueUsage {
    override val span: Span = andThenUsage.span
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return copy(usedAsType = mapper(usedAsType))
    }

    override fun describeForDiagnostic(descriptionOfUsedValue: String): String {
        return andThenUsage.describeForDiagnostic("a value derived from $descriptionOfUsedValue")
    }
}

/**
 * The value is used without any reference to it ever being created _anywhere_. This is the case e.g. for
 * object traversal: the object being traversed is used, and needs to be available/alive, but isn't borrowed or
 * captured in any way.
 */
data class TransientValueUsage(
    override val span: Span
) : ValueUsage {
    // currently, this is identical to IrrelevantValueUsage; though, a difference might be needed in some cases
    // to distinguish between the two different use cases of the two objects
    override val usedAsType: BoundTypeReference? = null
    override val usageOwnership = VariableOwnership.BORROWED
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage = this
    override fun describeForDiagnostic(descriptionOfUsedValue: String) = "transient usage of $descriptionOfUsedValue"
}

/**
 * Used in situations where the usage of a value cannot be determined. This object should behave in a way so that
 * it doesn't trigger any Diagnostics.
 */
object IrrelevantValueUsage : ValueUsage {
    override val usedAsType: BoundTypeReference? = null
    override val usageOwnership: VariableOwnership = VariableOwnership.BORROWED
    override val span = Span.UNKNOWN
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage = this
    override fun describeForDiagnostic(descriptionOfUsedValue: String): String = "unclassified usage of $descriptionOfUsedValue"
}
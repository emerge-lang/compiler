package compiler.binding.expression

import compiler.ast.VariableOwnership
import compiler.binding.BoundFunction
import compiler.binding.type.BoundTypeReference
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

    fun describeForDiagnostic(descriptionOfUsedValue: String): String = "!!UNDESCRIBED!!" // TODO: fully implement for all cases

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

internal data class ValueUsageImpl(
    override val usedAsType: BoundTypeReference?,
    override val usageOwnership: VariableOwnership,
    override val span: Span = Span.UNKNOWN, // TODO: remove default value and implement correctly everywhere
) : ValueUsage {
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return copy(usedAsType = mapper(usedAsType))
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
 * Used in situations where the usage of a value cannot be determined. This object should behave in a way so that
 * it doesn't trigger any Diagnostics.
 */
object IrrelevantValueUsage : ValueUsage {
    override val usedAsType: BoundTypeReference? = null
    override val usageOwnership: VariableOwnership = VariableOwnership.BORROWED
    override val span = Span.UNKNOWN
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage = this
}
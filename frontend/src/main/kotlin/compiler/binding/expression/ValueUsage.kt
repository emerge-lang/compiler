package compiler.binding.expression

import compiler.ast.VariableOwnership
import compiler.binding.type.BoundTypeReference

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
     * @return a [ValueUsage] identical to `this`, except that [usedAsType] has been transformed using [mapper].
     */
    fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage
}

internal data class ValueUsageImpl(override val usedAsType: BoundTypeReference?, override val usageOwnership: VariableOwnership) : ValueUsage {
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return ValueUsageImpl(mapper(usedAsType), usageOwnership)
    }
}
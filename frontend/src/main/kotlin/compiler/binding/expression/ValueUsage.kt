package compiler.binding.expression

import compiler.ast.VariableOwnership
import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundVariable
import compiler.binding.BoundVariableAssignmentStatement
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
     * @return a [ValueUsage] identical to `this`, except that [usedAsType] has been transformed using [mapper].
     */
    fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage
}

internal data class ValueUsageImpl(override val usedAsType: BoundTypeReference?, override val usageOwnership: VariableOwnership) : ValueUsage {
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }

        return copy(usedAsType = mapper(usedAsType))
    }
}

internal data class AssignmentToVariableValueUsage(
    override val usedAsType: BoundTypeReference?,
    val referencedVariable: BoundVariable?,
    val variableReferencedAt: Span,
) : ValueUsage {
    override val usageOwnership: VariableOwnership get() = referencedVariable?.ownershipAtDeclarationTime ?: VariableOwnership.BORROWED

    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage {
        if (usedAsType == null) {
            return this
        }
        return copy(usedAsType = mapper(usedAsType))
    }
}

/**
 * Used in situations where the usage of a value cannot be determined. This object should behave in a way so that
 * it doesn't trigger any Diagnostics.
 */
object IrrelevantValueUsage : ValueUsage {
    override val usedAsType: BoundTypeReference? = null
    override val usageOwnership: VariableOwnership = VariableOwnership.BORROWED
    override fun mapType(mapper: (BoundTypeReference) -> BoundTypeReference): ValueUsage = this
}
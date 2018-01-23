package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.MemberAccessExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.reportings.Reporting

class BoundMemberAccessExpression(
    override val context: CTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: BaseTypeReference? = null
        private set

    override val isGuaranteedToThrow = false // member accessor CAN throw, but must not ALWAYS do so

    override fun semanticAnalysisPhase1() = valueExpression.semanticAnalysisPhase1()
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        val valueType = valueExpression.type
        if (valueType != null) {
            if (valueType.isNullable && !isNullSafeAccess) {
                reportings.add(Reporting.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
                // TODO: set the type of this expression nullable
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                reportings.add(Reporting.superfluousNullSafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
            }
        }

        // TODO: resolve member
        // TODO: what about FQNs?

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findWritesBeyond(boundary)
    }
}
package compiler.binding.expression

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundMemberAccessExpression(
    override val context: CTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: BaseTypeReference? = null
        private set

    override fun semanticAnalysisPhase1() = valueExpression.semanticAnalysisPhase1()
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        // TODO: resolve member
        // TODO: what about FQNs?

        return reportings
    }
}
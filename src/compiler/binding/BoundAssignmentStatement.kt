package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.parser.Reporting

class BoundAssignmentStatement(
    override val context: CTContext,
    override val declaration: AssignmentStatement,
    val targetExpression: BoundExpression<*>,
    val valueExpression: BoundExpression<*>
) : BoundExecutable<AssignmentStatement> {

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings += targetExpression.semanticAnalysisPhase1()
        reportings += valueExpression.semanticAnalysisPhase2()

        // TODO
        // reject if the targetExpression does not point to something that
        // can or should be written to
        if (targetExpression is BoundIdentifierExpression) {
            // TODO find out what the identifier points to. If it is a variable this is fine for this phase
        }
        else if (targetExpression !is BoundMemberAccessExpression) {
            reportings += Reporting.error("Cannot assign to this target", declaration.targetExpression.sourceLocation)
        }

        return reportings
    }
}
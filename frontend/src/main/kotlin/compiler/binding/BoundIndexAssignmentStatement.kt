package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.ast.Statement
import compiler.binding.expression.BoundInvocationExpression
import compiler.reportings.FunctionMissingModifierReporting.Companion.requireOperatorModifier
import compiler.reportings.Reporting

class BoundIndexAssignmentStatement(
    override val declaration: AssignmentStatement,
    val hiddenInvocation: BoundInvocationExpression,
) : BoundStatement<Statement> by hiddenInvocation {
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = hiddenInvocation.semanticAnalysisPhase2().toMutableList()

        requireOperatorModifier(
            hiddenInvocation,
            this,
            reportings,
        )

        return  reportings
    }
}
package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.ast.Statement
import compiler.ast.expression.AstIndexAccessExpression
import compiler.binding.expression.BoundInvocationExpression
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.FunctionMissingModifierDiagnostic.Companion.requireOperatorModifier

class BoundIndexAssignmentStatement(
    override val declaration: AssignmentStatement<AstIndexAccessExpression>,
    val hiddenInvocation: BoundInvocationExpression,
) : BoundStatement<Statement> by hiddenInvocation {
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        hiddenInvocation.semanticAnalysisPhase2(diagnosis)
        requireOperatorModifier(
            hiddenInvocation,
            this,
            diagnosis,
        )
    }
}
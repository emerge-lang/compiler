package compiler.binding.expression

import compiler.ast.AstWhenExpression
import compiler.ast.Expression
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.InvocationJoinExecutionScopedCTContext
import compiler.binding.context.MultiBranchJoinExecutionScopedCTContext
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis

/**
 * @param desugared see [AstWhenExpression.bindTo]; bound to a scope of its own
 */
class BoundWhenExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstWhenExpression,
    val bindTimeDiagnosis: CollectingDiagnosis,
    val desugared: BoundCodeChunk,
) : BoundExpression<Expression> by desugared {
    /**
     * Leaves the scope of [desugared]: its variables are gone, its effects on [context] remain. The borrow of the
     * subject ends here, just like the borrows of arguments end when an invocation returns.
     */
    override val modifiedContext: ExecutionScopedCTContext = MultiBranchJoinExecutionScopedCTContext(
        context,
        listOf(InvocationJoinExecutionScopedCTContext(context, desugared.modifiedContext)),
    )

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        bindTimeDiagnosis.replayOnto(diagnosis)
        desugared.semanticAnalysisPhase1(diagnosis)
    }
}

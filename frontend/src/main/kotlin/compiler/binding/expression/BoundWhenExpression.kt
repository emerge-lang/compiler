package compiler.binding.expression

import compiler.ast.AstWhenExpression
import compiler.ast.Expression
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.InvocationJoinExecutionScopedCTContext
import compiler.binding.context.MultiBranchJoinExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.unreachableWhenElseBranch
import compiler.diagnostic.whenNotExhaustive

/**
 * @param exhaustiveness for a `when` with `is` branches, see [AstWhenExpression.bindTo]
 * @param desugared see [AstWhenExpression.bindTo]; bound to a scope of its own
 */
class BoundWhenExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstWhenExpression,
    val bindTimeDiagnosis: CollectingDiagnosis,
    private val exhaustiveness: WhenExhaustiveness?,
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

    private var isInExpressionContext = false

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        isInExpressionContext = true
        desugared.setExpectedEvaluationResultType(type, diagnosis)
    }

    override fun markEvaluationResultUsed() {
        isInExpressionContext = true
        desugared.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        desugared.semanticAnalysisPhase2(diagnosis)

        val exhaustiveness = exhaustiveness ?: return
        val result = exhaustiveness.result
        if (declaration.elseBranch != null) {
            if (result == WhenExhaustiveness.Result.Exhaustive) {
                diagnosis.unreachableWhenElseBranch(declaration.elseBranch.elseKeyword)
            }
            return
        }

        // same as for an if without else: a value of Unit is fine without covering all cases
        if (isInExpressionContext && !isUnitOrNothing(desugared.type)) {
            diagnosis.whenNotExhaustive(declaration.whenKeyword, result)
        }
    }

    private fun isUnitOrNothing(type: BoundTypeReference?): Boolean {
        val baseType = (type as? RootResolvedTypeReference)?.baseType ?: return type == null
        return baseType == context.swCtx.unit || baseType == context.swCtx.nothing
    }
}

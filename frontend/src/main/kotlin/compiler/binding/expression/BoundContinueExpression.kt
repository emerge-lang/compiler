package compiler.binding.expression

import compiler.ast.AstContinueExpression
import compiler.binding.BoundLoop
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.continueOutsideOfLoop
import compiler.util.mapToBackendIrWithDebugLocations
import io.github.tmarsteel.emerge.backend.api.ir.IrContinueStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundContinueExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstContinueExpression,
) : BoundScopeAbortingExpression() {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    private var parentLoop: BoundLoop<*>? = null

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parentLoop = context.parentLoop
        if (parentLoop == null) {
            diagnosis.continueOutsideOfLoop(this)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        // nothing to do
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // not relevant
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    private inner class IrContinueStatementImpl : IrContinueStatement {
        override val loop get() = parentLoop!!.irLoopNode
    }
    private val backendIr by lazy {
        IrCodeChunkImpl(
            listOfNotNull(parentLoop!!.irBeforeContinue) +
            context.getDeferredCodeForBreakOrContinue(parentLoop!!).mapToBackendIrWithDebugLocations() +
            IrContinueStatementImpl()
        )
    }
    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
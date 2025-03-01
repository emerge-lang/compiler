package compiler.binding.expression

import compiler.ast.AstBreakExpression
import compiler.binding.BoundLoop
import compiler.binding.ImpurityVisitor
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundBreakExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstBreakExpression,
) : BoundScopeAbortingExpression() {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    private var parentLoop: BoundLoop<*>? = null

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parentLoop = context.getParentLoop()
        if (parentLoop == null) {
            diagnosis.add(Reporting.breakOutsideOfLoop(this))
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // nothing to do
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    private inner class IrBreakStatementImpl : IrBreakStatement {
        override val fromLoop get() = parentLoop!!.toBackendIrStatement()
    }
    private val backendIr = IrBreakStatementImpl()
    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
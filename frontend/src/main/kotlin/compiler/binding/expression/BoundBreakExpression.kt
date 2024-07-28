package compiler.binding.expression

import compiler.ast.AstBreakExpression
import compiler.binding.BoundLoop
import compiler.binding.SideEffectPrediction
import compiler.binding.context.ExecutionScopedCTContext
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

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        parentLoop = context.getParentLoop()
        if (parentLoop == null) {
            reportings.add(Reporting.breakOutsideOfLoop(this))
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return emptySet()
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // nothing to do
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return emptySet()
    }

    private inner class IrBreakStatementImpl : IrBreakStatement {
        override val fromLoop get() = parentLoop!!.toBackendIrStatement()
    }
    private val backendIr = IrBreakStatementImpl()
    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
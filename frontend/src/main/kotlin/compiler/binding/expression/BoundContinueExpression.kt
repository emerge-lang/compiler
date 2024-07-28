package compiler.binding.expression

import compiler.ast.AstContinueExpression
import compiler.binding.BoundLoop
import compiler.binding.SideEffectPrediction
import compiler.binding.context.ExecutionScopedCTContext
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrContinueStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundContinueExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstContinueExpression,
) : BoundScopeAbortingExpression() {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    private var parentLoop: BoundLoop<*>? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        parentLoop = context.getParentLoop()
        if (parentLoop == null) {
            reportings.add(Reporting.continueOutsideOfLoop(this))
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

    private inner class IrContinueStatementImpl : IrContinueStatement {
        override val loop get() = parentLoop!!.toBackendIrStatement()
    }
    private val backendIr = IrContinueStatementImpl()
    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
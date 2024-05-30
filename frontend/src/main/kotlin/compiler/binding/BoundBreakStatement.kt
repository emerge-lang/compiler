package compiler.binding

import compiler.ast.AstBreakStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundBreakStatement(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstBreakStatement,
) : BoundStatement<AstBreakStatement> {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER
    override val implicitEvaluationResultType = null

    private var parentLoop: BoundLoop<*>? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        parentLoop = context.getParentLoop()
        if (parentLoop == null) {
            reportings.add(Reporting.breakOutsideOfLoop(this))
        }

        return reportings
    }

    private var implicitEvaluationRequired = false
    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
        implicitEvaluationRequired = true
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (implicitEvaluationRequired) {
            reportings.add(Reporting.implicitlyEvaluatingAStatement(this))
        }

        return reportings
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
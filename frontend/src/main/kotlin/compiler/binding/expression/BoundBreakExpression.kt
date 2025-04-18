package compiler.binding.expression

import compiler.ast.AstBreakExpression
import compiler.binding.BoundLoop
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.breakOutsideOfLoop
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
            diagnosis.breakOutsideOfLoop(this)
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

    private inner class IrBreakStatementImpl : IrBreakStatement {
        override val fromLoop get() = parentLoop!!.toBackendIrStatement()
    }
    private val backendIr = IrBreakStatementImpl()
    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
package compiler.binding

import compiler.ast.AstWhileLoop
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrWhileLoop

class BoundWhileLoop(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstWhileLoop,
    val condition: BoundCondition,
    val body: BoundCodeChunk,
) : BoundLoop<AstWhileLoop> {
    override val throwBehavior get() = condition.throwBehavior.combineSequentialExecution(body.throwBehavior)
    override val returnBehavior get() = condition.returnBehavior.combineSequentialExecution(body.returnBehavior)

    override val implicitEvaluationResultType = null

    override val modifiedContext = SingleBranchJoinExecutionScopedCTContext(
        context,
        body.modifiedContext,
    )

    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
        // nothing to do, loops don't evaluate to anything
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        condition.setNothrow(boundary)
        body.setNothrow(boundary)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableListOf<Reporting>()
            reportings.addAll(condition.semanticAnalysisPhase1())
            reportings.addAll(body.semanticAnalysisPhase1())

            return@phase1 reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = mutableListOf<Reporting>()
            reportings.addAll(condition.semanticAnalysisPhase2())
            reportings.addAll(body.semanticAnalysisPhase2())

            return@phase2 reportings
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        condition.setExpectedReturnType(type)
        body.setExpectedReturnType(type)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableListOf<Reporting>()
            reportings.addAll(condition.semanticAnalysisPhase3())
            reportings.addAll(body.semanticAnalysisPhase3())

            return@phase3 reportings
        }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return condition.findReadsBeyond(boundary) + body.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return condition.findWritesBeyond(boundary) + body.findWritesBeyond(boundary)
    }

    private val backendIr by lazy {
        IrWhileLoopImpl(condition.toBackendIrExpression(), body.toBackendIrStatement())
    }
    override fun toBackendIrStatement(): IrWhileLoop {
        return backendIr
    }
}

private class IrWhileLoopImpl(
    override val condition: IrExpression,
    override val body: IrCodeChunk,
) : IrWhileLoop
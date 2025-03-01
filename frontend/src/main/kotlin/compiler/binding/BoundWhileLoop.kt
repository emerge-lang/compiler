package compiler.binding

import compiler.ast.AstWhileLoop
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrConditionalBranchImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrLoopImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

class BoundWhileLoop(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstWhileLoop,
    val condition: BoundCondition,
    val body: BoundCodeChunk,
) : BoundLoop<AstWhileLoop> {
    override val throwBehavior get() = condition.throwBehavior.combineSequentialExecution(body.throwBehavior)
    override val returnBehavior get() = condition.returnBehavior.combineSequentialExecution(body.returnBehavior)

    override val modifiedContext = SingleBranchJoinExecutionScopedCTContext(
        context,
        body.modifiedContext,
    )

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        condition.setNothrow(boundary)
        body.setNothrow(boundary)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            condition.semanticAnalysisPhase1(diagnosis)
            body.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            condition.semanticAnalysisPhase2(diagnosis)
            body.semanticAnalysisPhase2(diagnosis)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        condition.setExpectedReturnType(type, diagnosis)
        body.setExpectedReturnType(type, diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            condition.semanticAnalysisPhase3(diagnosis)
            body.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun findReadsBeyond(boundary: CTContext, diagnosis: Diagnosis): Collection<BoundExpression<*>> {
        return condition.findReadsBeyond(boundary, diagnosis) + body.findReadsBeyond(boundary, diagnosis)
    }

    override fun findWritesBeyond(boundary: CTContext, diagnosis: Diagnosis): Collection<BoundExecutable<*>> {
        return condition.findWritesBeyond(boundary, diagnosis) + body.findWritesBeyond(boundary, diagnosis)
    }

    private val backendIr by lazy {
        val conditionTemporary = IrCreateTemporaryValueImpl(condition.toBackendIrExpression())
        lateinit var irLoop: IrLoop
        val breakStmt = object : IrBreakStatement {
            override val fromLoop get() = irLoop
        }
        irLoop = IrLoopImpl(
            IrCodeChunkImpl(listOf(
                conditionTemporary,
                IrConditionalBranchImpl(
                    condition = IrTemporaryValueReferenceImpl(conditionTemporary),
                    thenBranch = body.toBackendIrStatement(),
                    elseBranch = breakStmt,
                )
            ))
        )

        irLoop
    }
    override fun toBackendIrStatement(): IrLoop {
        return backendIr
    }
}
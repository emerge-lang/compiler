package compiler.binding

import compiler.ast.AstDoWhileLoop
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.expression.IrConditionalBranchImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrLoopImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrContinueStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

class BoundDoWhileLoop(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstDoWhileLoop,
    val condition: BoundCondition,
    val body: BoundCodeChunk,
) : BoundLoop<AstDoWhileLoop> {
    override val throwBehavior get() = body.throwBehavior.combineSequentialExecution(condition.throwBehavior)
    override val returnBehavior get() = body.returnBehavior.combineSequentialExecution(condition.returnBehavior)

    override val modifiedContext = SingleBranchJoinExecutionScopedCTContext(
        context,
        condition.modifiedContext,
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

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        condition.visitReadsBeyond(boundary, visitor)
        body.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        condition.visitWritesBeyond(boundary, visitor, diagnosis)
        body.visitWritesBeyond(boundary, visitor, diagnosis)
    }

    private val backendIr by lazy {
        lateinit var loopHolder: IrLoop
        val continueStmt = object : IrContinueStatement {
            override val loop get()= loopHolder
        }
        val breakStmt = object : IrBreakStatement {
            override val fromLoop get() = loopHolder
        }
        val conditionTemporary = IrCreateTemporaryValueImpl(condition.toBackendIrExpression())
        loopHolder = IrLoopImpl(IrCodeChunkImpl(listOf(
            body.toBackendIrStatement(),
            conditionTemporary,
            IrConditionalBranchImpl(
                condition = IrTemporaryValueReferenceImpl(conditionTemporary),
                thenBranch = continueStmt,
                elseBranch = breakStmt
            )
        )))

        loopHolder
    }
    override fun toBackendIrStatement(): IrLoop {
        return backendIr
    }
}
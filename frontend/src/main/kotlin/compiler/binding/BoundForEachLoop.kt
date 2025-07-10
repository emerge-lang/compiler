package compiler.binding

import compiler.ast.AstForEachLoop
import compiler.binding.SideEffectPrediction.Companion.reduceSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrLoopImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnosis.Companion.doWithIgnoringFindings
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

class BoundForEachLoop(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstForEachLoop,
    val iterableExpression: BoundExpression<*>,
    val rangeHolderDeclaration: BoundVariable,
    val cursorInBodyDeclaration: BoundVariable,
    val advanceRange: BoundExecutable<*>,
    val body: BoundCodeChunk,
) : BoundLoop<AstForEachLoop> {
    override val throwBehavior: SideEffectPrediction?
        get() = listOf(rangeHolderDeclaration.throwBehavior, cursorInBodyDeclaration.throwBehavior, body.throwBehavior, advanceRange.throwBehavior)
            .reduceSequentialExecution()
    override val returnBehavior: SideEffectPrediction?
        get() = listOf(rangeHolderDeclaration.returnBehavior, cursorInBodyDeclaration.returnBehavior, body.returnBehavior, advanceRange.returnBehavior)
            .reduceSequentialExecution()

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        rangeHolderDeclaration.setNothrow(boundary)
        cursorInBodyDeclaration.setNothrow(boundary)
        advanceRange.setNothrow(boundary)
        body.setNothrow(boundary)
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            rangeHolderDeclaration.semanticAnalysisPhase1(diagnosis)
            cursorInBodyDeclaration.semanticAnalysisPhase1(diagnosis)
            advanceRange.semanticAnalysisPhase1(diagnosis)
            body.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            iterableExpression.semanticAnalysisPhase2(diagnosis)
            val notAnIterableError = iterableExpression.type?.evaluateAssignabilityTo(context.swCtx.iterable.baseReference, iterableExpression.declaration.span)
            if (notAnIterableError == null) {
                rangeHolderDeclaration.semanticAnalysisPhase2(diagnosis)
            } else {
                diagnosis.add(notAnIterableError)
                diagnosis.doWithIgnoringFindings(rangeHolderDeclaration::semanticAnalysisPhase2)
            }
            cursorInBodyDeclaration.semanticAnalysisPhase2(diagnosis)
            advanceRange.semanticAnalysisPhase2(diagnosis)
            body.semanticAnalysisPhase2(diagnosis)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            rangeHolderDeclaration.semanticAnalysisPhase3(diagnosis)
            cursorInBodyDeclaration.semanticAnalysisPhase3(diagnosis)
            advanceRange.semanticAnalysisPhase3(diagnosis)
            body.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun visitReadsBeyond(
        boundary: CTContext,
        visitor: ImpurityVisitor,
    ) {
        rangeHolderDeclaration.visitReadsBeyond(boundary, visitor)
        body.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(
        boundary: CTContext,
        visitor: ImpurityVisitor,
    ) {
        rangeHolderDeclaration.visitWritesBeyond(boundary, visitor)
        body.visitWritesBeyond(boundary, visitor)
    }

    private val _modifiedContext = MutableExecutionScopedCTContext.deriveFrom(SingleBranchJoinExecutionScopedCTContext(
        context,
        body.modifiedContext,
    ))
    override val modifiedContext: ExecutionScopedCTContext = _modifiedContext

    override fun setExpectedReturnType(
        type: BoundTypeReference,
        diagnosis: Diagnosis,
    ) {
        rangeHolderDeclaration.setExpectedReturnType(type, diagnosis)
        cursorInBodyDeclaration.setExpectedReturnType(type, diagnosis)
        advanceRange.setExpectedReturnType(type, diagnosis)
        body.setExpectedReturnType(type, diagnosis)
    }

    override lateinit var irLoopNode: IrLoop
        private set
    override lateinit var irBeforeContinue: IrExecutable
        private set

    private val backendIr: IrCodeChunk by lazy {
        var cursorInBodyIr = cursorInBodyDeclaration.toBackendIrStatement()
        irBeforeContinue = advanceRange.toBackendIrStatement()
        var actualBodyIr = body.toBackendIrStatement()
        irLoopNode = IrLoopImpl(IrCodeChunkImpl(listOf(
            cursorInBodyIr, actualBodyIr, irBeforeContinue
        )))

        IrCodeChunkImpl(listOf(
            rangeHolderDeclaration.toBackendIrStatement(),
            irLoopNode,
        ))
    }

    override fun toBackendIrStatement(): IrExecutable {
        return backendIr
    }
}
package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.expression.AstCatchBlockExpression
import compiler.ast.type.TypeMutability
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.DropLocalVariableStatement
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundCatchBlockExpression(
    override val context: ExecutionScopedCTContext,
    private val contextOfCatchCode: MutableExecutionScopedCTContext,
    override val declaration: AstCatchBlockExpression,
    val throwableVariable: BoundVariable,
    val catchCode: BoundCodeChunk,
) : BoundExpression<AstCatchBlockExpression> {
    init {
        check(!throwableVariable.isReAssignable) {
            "catch variable is reassignable, this is is definitely wrong!"
        }
    }

    override val modifiedContext = context
    init {
        contextOfCatchCode.addDeferredCode(DropLocalVariableStatement(throwableVariable))
    }

    override val throwBehavior get() = catchCode.throwBehavior
    override val returnBehavior get() = catchCode.returnBehavior

    override val type get() = catchCode.type
    override val isEvaluationResultReferenceCounted: Boolean
        get() = catchCode.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored: Boolean
        get() = catchCode.isEvaluationResultAnchored
    override val isCompileTimeConstant: Boolean
        get() = catchCode.isCompileTimeConstant

    val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            throwableVariable.semanticAnalysisPhase1(diagnosis)
            catchCode.semanticAnalysisPhase1(diagnosis)

            // this is done by the backend
            contextOfCatchCode.trackSideEffect(
                VariableInitialization.WriteToVariableEffect(throwableVariable)
            )

            return@phase1 reportings
        }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        catchCode.setExpectedEvaluationResultType(type)
    }

    override fun markEvaluationResultUsed() {

    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            throwableVariable.semanticAnalysisPhase2(diagnosis)
            catchCode.semanticAnalysisPhase2(diagnosis)
            return@phase2 reportings
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        catchCode.setExpectedReturnType(type)
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // note that not even a catch-all can turn throwing code into nothrow code!
        // objects of type emerge.core.Error cannot be caught
        catchCode.setNothrow(boundary)
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return catchCode.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<*>> {
        return catchCode.findWritesBeyond(boundary)
    }

    override fun markEvaluationResultCaptured(withMutability: TypeMutability) {
        catchCode.markEvaluationResultCaptured(withMutability)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            throwableVariable.semanticAnalysisPhase3(diagnosis)
            catchCode.semanticAnalysisPhase3(diagnosis)
            return@phase3 reportings
        }
    }

    override fun toBackendIrStatement(): IrExecutable {
        throw InternalCompilerError("this should never be called; instead, access ${this::catchCode.name} and ${this::throwableVariable.name} directly")
    }

    override fun toBackendIrExpression(): IrExpression {
        throw InternalCompilerError("this should never be called; instead, access ${this::catchCode.name} and ${this::throwableVariable.name} directly")
    }
}
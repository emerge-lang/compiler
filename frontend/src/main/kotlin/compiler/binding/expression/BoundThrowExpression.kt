package compiler.binding.expression

import compiler.ast.AstThrowExpression
import compiler.ast.type.TypeMutability
import compiler.binding.ImpurityVisitor
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrExpressionSideEffectsStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrThrowStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class BoundThrowExpression(
    override val context: ExecutionScopedCTContext,
    val throwableExpression: BoundExpression<*>,
    override val declaration: AstThrowExpression,
) : BoundScopeAbortingExpression() {
    override val throwBehavior = SideEffectPrediction.GUARANTEED
    override val returnBehavior = SideEffectPrediction.NEVER

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            throwableExpression.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {

            val expectedType = context.swCtx.throwable.baseReference.withMutability(TypeMutability.READONLY)
            throwableExpression.setExpectedEvaluationResultType(expectedType, diagnosis)
            throwableExpression.semanticAnalysisPhase2(diagnosis)
            throwableExpression.type
                ?.evaluateAssignabilityTo(expectedType, throwableExpression.declaration.span)
                ?.let(diagnosis::add)
        }
    }

    private var nothrowBoundary: NothrowViolationReporting.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        this.nothrowBoundary = boundary
        this.throwableExpression.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            throwableExpression.semanticAnalysisPhase3(diagnosis)
            nothrowBoundary?.let { nothrowBoundary ->
                diagnosis.add(Reporting.throwStatementInNothrowContext(this, nothrowBoundary))
            }
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        throwableExpression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        throwableExpression.visitWritesBeyond(boundary, visitor)
    }

    private val _backendIr: IrExecutable by lazy {
        return@lazy buildIrThrow(
            context,
            throwableExpression.toBackendIrExpression(),
            throwableExpression.isEvaluationResultReferenceCounted,
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        return _backendIr
    }
}

internal fun buildIrThrow(
    context: ExecutionScopedCTContext,
    throwableExpression: IrExpression,
    throwableInstanceIsReferenceCounted: Boolean,
): IrExecutable {
    val throwableInstance = IrCreateTemporaryValueImpl(throwableExpression)

    // calling fillStackTrace can throw an exception; that should be ignored. But it needs to be properly dropped/refcounted,
    // so that is more elaborate here; might make sense to look into addSuppressed like Java has
    val varDeclExceptionFromFillStackTrace = object : IrVariableDeclaration {
        override val name = context.findInternalVariableName("fillStackTraceException")
        override val type: IrType = context.swCtx.throwable.baseReference.toBackendIr()
        override val isBorrowed = false
        override val isReAssignable = false
        override val isSSA = true
    }
    val fillStackTraceExceptionTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(varDeclExceptionFromFillStackTrace))
    val fillStackTraceLandingpad = IrInvocationExpression.Landingpad(
        // for now, just ignore any throwable that results from the fillStackTrace call,
        varDeclExceptionFromFillStackTrace,
        IrCodeChunkImpl(listOf(
            fillStackTraceExceptionTemporary,
            IrDropStrongReferenceStatementImpl(fillStackTraceExceptionTemporary),
            IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
        )),
    )

    val fillStackTraceCall = IrExpressionSideEffectsStatementImpl(IrDynamicDispatchFunctionInvocationImpl(
        IrTemporaryValueReferenceImpl(throwableInstance),
        context.swCtx.throwable.memberFunctions
            .single { it.canonicalName.simpleName == "fillStackTrace" && it.parameterCount == 1 }
            .overloads
            .single()
            .toBackendIr(),
        listOf(IrTemporaryValueReferenceImpl(throwableInstance)),
        emptyMap(),
        context.swCtx.unit.baseReference.toBackendIr(),
        fillStackTraceLandingpad,
    ))

    val cleanupCode = (context.getExceptionHandlingLocalDeferredCode() + context.getDeferredCodeForThrow())
        .map { it.toBackendIrStatement() }
        .toList()

    return IrCodeChunkImpl(listOfNotNull(
        throwableInstance,
        IrCreateStrongReferenceStatementImpl(throwableInstance).takeUnless { throwableInstanceIsReferenceCounted },
    ) + cleanupCode + listOf(
        fillStackTraceCall,
        IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
    ))
}

internal class IrThrowStatementImpl(
    override val throwable: IrTemporaryValueReference
) : IrThrowStatement
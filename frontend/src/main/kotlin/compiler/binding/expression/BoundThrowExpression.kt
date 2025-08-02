package compiler.binding.expression

import compiler.ast.AstThrowExpression
import compiler.ast.type.TypeMutability
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrExpressionSideEffectsStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.throwStatementInNothrowContext
import compiler.lexer.Span
import compiler.util.mapToBackendIrWithDebugLocations
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
    override val modifiedContext: ExecutionScopedCTContext = run {
        val newCtx = MutableExecutionScopedCTContext.deriveFrom(throwableExpression.modifiedContext)
        newCtx.trackSideEffect(CallFrameExit.Effect.Throws)
        newCtx
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            throwableExpression.semanticAnalysisPhase1(diagnosis)
            throwableExpression.markEvaluationResultUsed()
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            val expectedType = context.swCtx.throwable
                .getBoundReferenceAssertNoTypeParameters(declaration.throwKeyword.span)
                .withMutability(TypeMutability.MUTABLE)
            throwableExpression.setExpectedEvaluationResultType(expectedType, diagnosis)
            throwableExpression.semanticAnalysisPhase2(diagnosis)
            throwableExpression.type
                ?.evaluateAssignabilityTo(expectedType, throwableExpression.declaration.span)
                ?.let(diagnosis::add)

            throwableExpression.setEvaluationResultUsage(ThrowValueUsage(
                expectedType,
                declaration.throwKeyword.span,
            ))
        }
    }

    private var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        this.nothrowBoundary = boundary
        this.throwableExpression.setNothrow(boundary)
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // nothing to do; the evaluation result type of "throw" is Nothing
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            throwableExpression.semanticAnalysisPhase3(diagnosis)
            nothrowBoundary?.let { nothrowBoundary ->
                diagnosis.throwStatementInNothrowContext(this, nothrowBoundary)
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
            declaration.span,
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
    throwLocation: Span,
): IrExecutable {
    val throwLocationStatement = IrUpdateSourceLocationStatementImpl(throwLocation)
    val throwableInstance = IrCreateTemporaryValueImpl(throwableExpression)

    // calling fillStackTrace can throw an exception; that should be ignored. But it needs to be properly dropped/refcounted,
    // so that is more elaborate here; might make sense to look into addSuppressed like Java has
    val varDeclExceptionFromFillStackTrace = object : IrVariableDeclaration {
        override val name = context.findInternalVariableName("fillStackTraceException")
        override val type: IrType = context.swCtx.throwable.irReadNotNullReference
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
        context.swCtx.unit.irReadNotNullReference,
        fillStackTraceLandingpad,
    ))

    val cleanupCode = (context.getExceptionHandlingLocalDeferredCode() + context.getDeferredCodeForThrow())
        .mapToBackendIrWithDebugLocations()

    return IrCodeChunkImpl(listOfNotNull(
        throwableInstance,
        IrCreateStrongReferenceStatementImpl(throwableInstance).takeUnless { throwableInstanceIsReferenceCounted },
    ) + cleanupCode + listOf(
        throwLocationStatement,
        fillStackTraceCall,
        throwLocationStatement,
        IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
    ))
}

internal class IrThrowStatementImpl(
    override val throwable: IrTemporaryValueReference,
    override val ignoreLocalCatchBlock: Boolean = false,
) : IrThrowStatement
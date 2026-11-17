package compiler.binding.expression

import io.github.tmarsteel.emerge.common.EmergeConstants
import compiler.InternalCompilerError
import compiler.ast.AstThrowExpression
import compiler.ast.type.TypeMutability
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.type.isAssignableTo
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
            throwableIsStaticallyAnError = throwableExpression.type?.isAssignableTo(
                context.swCtx.error.getBoundReferenceAssertNoTypeParameters().withMutability(TypeMutability.READONLY)
            ) == true,
            declaration.span,
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        return _backendIr
    }
}

/**
 * @param throwableIsStaticallyAnError whether the static type of [throwableExpression] is a subtype of
 * `emerge.core.Error`. If not, and if the throw is inside a `try` block, that is checked at runtime: an `Error`
 * is not to be caught, it must not go to the `catch`.
 */
internal fun buildIrThrow(
    context: ExecutionScopedCTContext,
    throwableExpression: IrExpression,
    throwableInstanceIsReferenceCounted: Boolean,
    throwableIsStaticallyAnError: Boolean,
    throwLocation: Span,
): IrExecutable {
    val throwLocationStatement = IrUpdateSourceLocationStatementImpl(throwLocation)
    val throwableInstance = IrCreateTemporaryValueImpl(throwableExpression)

    val cleanupCode = (context.getExceptionHandlingLocalDeferredCode() + context.getDeferredCodeForThrow())
        .mapToBackendIrWithDebugLocations()

    // same as the landingpad of an invocation (see buildGenericInvocationLikeIr): Errors pass by the catch.
    // They leave the function, so the scopes around the try have to be cleaned up, too.
    // Builds new IR on every call, as the code is needed twice: after fillStackTrace returns, and in its landingpad
    fun buildThrowCode(): List<IrExecutable> {
        if (!context.isInTryContext) {
            return listOf(IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance)))
        }

        val throwPastCatch = IrCodeChunkImpl(
            context.getDeferredCodeForUncatchableThrow().mapToBackendIrWithDebugLocations()
            +
            listOf(IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance), ignoreLocalCatchBlock = true))
        )
        if (throwableIsStaticallyAnError) {
            return listOf(throwPastCatch)
        }

        val isError = IrCreateTemporaryValueImpl(buildInstanceOf(
            context.swCtx,
            IrTemporaryValueReferenceImpl(throwableInstance),
            context.swCtx.error.getBoundReferenceAssertNoTypeParameters(),
            null,
        ))
        return listOf(
            isError,
            IrConditionalBranchImpl(
                condition = IrTemporaryValueReferenceImpl(isError),
                thenBranch = throwPastCatch,
                elseBranch = IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance)),
            ),
        )
    }

    // calling fillStackTrace can throw an exception; that should be ignored. But it needs to be properly dropped/refcounted,
    // so that is more elaborate here; might make sense to look into addSuppressed like Java has
    val varDeclExceptionFromFillStackTrace = object : IrVariableDeclaration {
        override val name = context.findInternalVariableName("fillStackTraceException")
        override val type: IrType = context.swCtx.throwable.irReadNotNullReference
        override val isBorrowed = false
        override val isReAssignable = false
        override val isSSA = true
        override val declaredAt = throwLocation
        override val scope get()= context.parentScopeContext!!.irScope
    }
    val fillStackTraceExceptionTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(varDeclExceptionFromFillStackTrace))
    val fillStackTraceLandingpad = IrInvocationExpression.Landingpad(
        // for now, just ignore any throwable that results from the fillStackTrace call,
        varDeclExceptionFromFillStackTrace,
        IrCodeChunkImpl(listOf(
            fillStackTraceExceptionTemporary,
            IrDropStrongReferenceStatementImpl(fillStackTraceExceptionTemporary),
        ) + buildThrowCode()),
    )

    val fillStackTraceFn = context.swCtx.getPackage(EmergeConstants.UnwindModule.NAME)
        ?.getTopLevelFunctionOverloadSetsBySimpleName(EmergeConstants.UnwindModule.FILL_STACK_TRACE_ON_THROW_FN_NAME.simpleName)
        ?.singleOrNull()
        ?.overloads
        ?.singleOrNull()
        ?: throw InternalCompilerError("Did not find ${EmergeConstants.UnwindModule.FILL_STACK_TRACE_ON_THROW_FN_NAME}")
    val fillStackTraceCall = IrExpressionSideEffectsStatementImpl(IrStaticDispatchFunctionInvocationImpl(
        fillStackTraceFn.toBackendIr(),
        listOf(IrTemporaryValueReferenceImpl(throwableInstance)),
        emptyMap(),
        context.swCtx.unit.irReadNotNullReference,
        fillStackTraceLandingpad,
    ))

    return IrCodeChunkImpl(listOfNotNull(
        throwableInstance,
        IrCreateStrongReferenceStatementImpl(throwableInstance).takeUnless { throwableInstanceIsReferenceCounted },
    ) + cleanupCode + listOf(
        throwLocationStatement,
        fillStackTraceCall,
        throwLocationStatement,
    ) + buildThrowCode())
}

internal class IrThrowStatementImpl(
    override val throwable: IrTemporaryValueReference,
    override val ignoreLocalCatchBlock: Boolean = false,
) : IrThrowStatement
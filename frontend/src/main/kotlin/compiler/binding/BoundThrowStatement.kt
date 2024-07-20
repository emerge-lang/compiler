package compiler.binding

import compiler.ast.AstThrowStatement
import compiler.ast.type.TypeMutability
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrDynamicDispatchFunctionInvocationImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrExpressionSideEffectsStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrThrowStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class BoundThrowStatement(
    override val context: ExecutionScopedCTContext,
    val throwableExpression: BoundExpression<*>,
    override val declaration: AstThrowStatement,
) : BoundStatement<AstThrowStatement> {
    override val throwBehavior = SideEffectPrediction.GUARANTEED
    override val returnBehavior = SideEffectPrediction.NEVER

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return throwableExpression.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        val expectedType = context.swCtx.throwable.baseReference.withMutability(TypeMutability.READONLY)
        throwableExpression.setExpectedEvaluationResultType(expectedType)
        reportings.addAll(throwableExpression.semanticAnalysisPhase2())
        throwableExpression.type
            ?.evaluateAssignabilityTo(expectedType, throwableExpression.declaration.span)
            ?.let(reportings::add)

        return reportings
    }

    private var nothrowBoundary: NothrowViolationReporting.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        this.nothrowBoundary = boundary
        this.throwableExpression.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(throwableExpression.semanticAnalysisPhase3())
        nothrowBoundary?.let { nothrowBoundary ->
            reportings.add(Reporting.throwStatementInNothrowContext(this, nothrowBoundary))
        }

        return reportings
    }

    override fun toBackendIrStatement(): IrExecutable {
        val throwableInstance = IrCreateTemporaryValueImpl(throwableExpression.toBackendIrExpression())
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
            IrInvocationExpression.Landingpad(
                // for now, just ignore any throwable that results from the fillStackTrace call, might make sense
                // to look into addSuppressed like Java has
                object : IrVariableDeclaration {
                    override val name = "_"
                    override val type: IrType = context.swCtx.throwable.baseReference.toBackendIr()
                    override val isBorrowed = false
                    override val isReAssignable= false
                },
                IrCodeChunkImpl(listOf(
                    IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
                )),
            )
        ))
        return IrCodeChunkImpl(listOf(
            throwableInstance,
            fillStackTraceCall,
            IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
        ))
    }
}

internal class IrThrowStatementImpl(
    override val throwable: IrTemporaryValueReference
) : IrThrowStatement
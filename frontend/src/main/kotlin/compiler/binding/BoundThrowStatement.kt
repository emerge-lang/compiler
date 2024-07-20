package compiler.binding

import compiler.ast.AstThrowStatement
import compiler.ast.type.TypeMutability
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrThrowStatement

class BoundThrowStatement(
    override val context: ExecutionScopedCTContext,
    val throwableExpression: BoundExpression<*>,
    override val declaration: AstThrowStatement,
) : BoundStatement<AstThrowStatement> {
    override val throwBehavior = SideEffectPrediction.GUARANTEED
    override val returnBehavior = SideEffectPrediction.NEVER
    override val implicitEvaluationResultType = null

    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {

    }

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
        return IrCodeChunkImpl(listOf(
            throwableInstance,
            IrThrowStatementImpl(IrTemporaryValueReferenceImpl(throwableInstance))
        ))
    }
}

internal class IrThrowStatementImpl(
    override val throwable: IrTemporaryValueReference
) : IrThrowStatement
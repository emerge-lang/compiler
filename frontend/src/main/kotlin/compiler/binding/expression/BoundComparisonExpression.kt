package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.lexer.NumericLiteralToken
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNumericComparisonExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundComparisonExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val hiddenCompareInvocation: BoundInvocationExpression,
    val predicate: IrNumericComparisonExpression.Predicate,
) : BoundExpression<Expression> by hiddenCompareInvocation {
    override val type get() = context.swCtx.bool.baseReference

    private val boundZeroConstant = NumericLiteralExpression(
        NumericLiteralToken(declaration.span.deriveGenerated(), "0")
    ).bindTo(context)

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return hiddenCompareInvocation.semanticAnalysisPhase1() +
                boundZeroConstant.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(hiddenCompareInvocation.semanticAnalysisPhase2())
        hiddenCompareInvocation.type?.also(boundZeroConstant::setExpectedEvaluationResultType)
        reportings.addAll(boundZeroConstant.semanticAnalysisPhase2())
        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return hiddenCompareInvocation.semanticAnalysisPhase3() +
                boundZeroConstant.semanticAnalysisPhase3()
    }

    override fun toBackendIrExpression(): IrExpression {
        val lhsTemporary = IrCreateTemporaryValueImpl(
            hiddenCompareInvocation.toBackendIrExpression()
        )
        val rhsTemporary = IrCreateTemporaryValueImpl(
            boundZeroConstant.toBackendIrExpression()
        )
        val comparisonTemporary = IrCreateTemporaryValueImpl(
            IrNumericComparisonExpressionImpl(
                IrTemporaryValueReferenceImpl(lhsTemporary),
                IrTemporaryValueReferenceImpl(rhsTemporary),
                predicate,
                context.swCtx.bool.baseReference.toBackendIr(),
            )
        )

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(
                listOf(
                    lhsTemporary,
                    rhsTemporary,
                    comparisonTemporary,
                )
            ),
            IrTemporaryValueReferenceImpl(comparisonTemporary),
        )
    }
}

private class IrNumericComparisonExpressionImpl(
    override val lhs: IrTemporaryValueReference,
    override val rhs: IrTemporaryValueReference,
    override val predicate: IrNumericComparisonExpression.Predicate,
    override val evaluatesTo: IrType,
) : IrNumericComparisonExpression
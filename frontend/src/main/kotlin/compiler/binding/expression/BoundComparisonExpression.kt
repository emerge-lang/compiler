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
        /*
        For numeric comparisons, this entire "call compareTo, which does a subtraction, and then compare that to 0"
        seems overkill - and it is! Luckily, this exact way of abstracting comparisons is prevalent in imperative languages
        since multiple decades; because of that, LLVM is optimized to understand what is going on and simplify to a
        single icmp/fcmp opcode: (even at optmization level 1 of 3!)

        %tmp1 = call i32 @llvm.ssub.sat.i32(i32 %lhs, i32 %rhs)
        %tmp2 = icmp sgt i32 %tmp1, 0

        gets optimized to

        %tmp2 = icmp sgt i32 %lhs, i32 %rhs

        HOWEVER! This stops to work even at -O3 if we add a sext to the word type; hence, the compareTo functions
        of the emerge number types always return their own signed variant (instead of a more homogenous SWord)
         */

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
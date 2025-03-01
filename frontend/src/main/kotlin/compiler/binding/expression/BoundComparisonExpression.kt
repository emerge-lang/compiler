package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.diagnostic.Diagnosis
import compiler.lexer.NumericLiteralToken
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

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        hiddenCompareInvocation.semanticAnalysisPhase1(diagnosis)
        boundZeroConstant.semanticAnalysisPhase1(diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        hiddenCompareInvocation.semanticAnalysisPhase2(diagnosis)
        hiddenCompareInvocation.type?.let { compareResultType ->
            boundZeroConstant.setExpectedEvaluationResultType(compareResultType, diagnosis)
        }
        boundZeroConstant.semanticAnalysisPhase2(diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        hiddenCompareInvocation.semanticAnalysisPhase3(diagnosis)
        boundZeroConstant.semanticAnalysisPhase3(diagnosis)
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

        SECOND CATCH: this trick doesn't work for unsigned types. An optimization would obviously have to be implemented
        here, whenever i feel like it.
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
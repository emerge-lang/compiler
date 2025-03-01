package compiler.binding.expression

import compiler.ast.expression.StringLiteralExpression
import compiler.ast.type.TypeMutability
import compiler.binding.SideEffectPrediction
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundStringLiteralExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: StringLiteralExpression,
) : BoundLiteralExpression<StringLiteralExpression> {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER
    override var type: BoundTypeReference? = null

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        type = context.swCtx.string.baseReference.withMutability(TypeMutability.IMMUTABLE)
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {}
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // nothing to do
    }

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = true

    override fun toBackendIrExpression(): IrExpression = IrStringLiteralExpressionImpl(
        declaration.content.content.encodeToByteArray(),
        type!!.toBackendIr(),
    )
}

internal class IrStringLiteralExpressionImpl(
    override val utf8Bytes: ByteArray,
    override val evaluatesTo: IrType
) : IrStringLiteralExpression {

}
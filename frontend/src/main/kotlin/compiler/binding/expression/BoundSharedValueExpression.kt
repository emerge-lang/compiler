package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.Expression
import compiler.ast.expression.AstSharedValueExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

/**
 * The one evaluation of an [AstSharedValueExpression]; holds the result in a temporary that the
 * [BoundSharedValueReference]s read.
 */
class BoundSharedValueExpression(
    val value: BoundExpression<*>,
) : BoundExpression<Expression> by value {
    private var irTemporary: IrCreateTemporaryValue? = null

    val evaluatedTemporary: IrCreateTemporaryValue
        get() = irTemporary ?: throw InternalCompilerError("A reference to a shared value is evaluated before the shared value itself")

    override fun toBackendIrExpression(): IrExpression {
        val temporary = IrCreateTemporaryValueImpl(value.toBackendIrExpression())
        irTemporary = temporary
        return IrImplicitEvaluationExpressionImpl(IrCodeChunkImpl(listOf(temporary)), IrTemporaryValueReferenceImpl(temporary))
    }
}

/**
 * Reads the result of a [BoundSharedValueExpression]. The [BoundSharedValueExpression] does all semantic analysis
 * and keeps the value alive; this is just another read of it.
 */
class BoundSharedValueReference(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstSharedValueExpression,
    private val sharedValue: BoundSharedValueExpression,
) : BoundExpression<AstSharedValueExpression> {
    override val type: BoundTypeReference? get() = sharedValue.type
    override val modifiedContext get() = context

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) = Unit
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) = Unit
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) = Unit
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit
    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = false

    override fun toBackendIrExpression(): IrExpression {
        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(emptyList()),
            IrTemporaryValueReferenceImpl(sharedValue.evaluatedTemporary),
        )
    }
}

package compiler.binding.expression

import compiler.binding.IrCodeChunkImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import compiler.ast.Expression as AstExpression

/**
 * code reuse superclass for scope aborting statements that always transfer control flow away from the scope and
 * have it not return
 */
abstract class BoundScopeAbortingExpression() : BoundExpression<AstExpression> {
    final override val type: BoundTypeReference by lazy {
        context.swCtx.bottomTypeRef
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // not relevant
    }

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = false
    override val isCompileTimeConstant = false

    override fun toBackendIrExpression(): IrExpression {
        val dummyValue = IrCreateTemporaryValueImpl(
            IrStaticDispatchFunctionInvocationImpl(
                context.swCtx.unit.resolveMemberFunction("instance")
                    .single { it.parameterCount == 0 }
                    .overloads
                    .single()
                    .toBackendIr(),
                emptyList(),
                emptyMap(),
                context.swCtx.unit.baseReference.toBackendIr(),
                null,
            )
        )

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(this.toBackendIrStatement(), dummyValue)),
            IrTemporaryValueReferenceImpl(dummyValue),
        )
    }
}
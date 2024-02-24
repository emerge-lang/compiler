package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class IrImplicitEvaluationExpressionImpl(
    override val code: IrCodeChunk,
    override val implicitValue: IrTemporaryValueReference,
) : IrImplicitEvaluationExpression {
    init {
        require(code.components.count { it === implicitValue.declaration } == 1)
    }
}
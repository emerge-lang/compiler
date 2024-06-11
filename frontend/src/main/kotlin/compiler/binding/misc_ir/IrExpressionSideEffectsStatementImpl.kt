package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpressionSideEffectsStatement

class IrExpressionSideEffectsStatementImpl(
    override val expression: IrExpression,
) : IrExpressionSideEffectsStatement
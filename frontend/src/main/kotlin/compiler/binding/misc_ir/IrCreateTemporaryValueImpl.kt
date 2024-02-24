package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

internal class IrCreateTemporaryValueImpl(
    override val value: IrExpression
) : IrCreateTemporaryValue
package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

internal class IrCreateTemporaryValueImpl(
    override val value: IrExpression,
    private val typeOverride: IrType? = null
) : IrCreateTemporaryValue {
    override val type get() = typeOverride ?: super.type
}
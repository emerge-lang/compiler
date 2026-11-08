package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrReifiedTypeExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

internal class IrReifiedTypeExpressionImpl(
    override val type: IrType,
    override val evaluatesTo: IrType,
) : IrReifiedTypeExpression

package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

internal class IrTemporaryValueReferenceImpl(
    override val declaration: IrCreateTemporaryValue,
) : IrTemporaryValueReference
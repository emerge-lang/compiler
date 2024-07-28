package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

internal class IrLoopImpl(
    override val body: IrExecutable,
) : IrLoop
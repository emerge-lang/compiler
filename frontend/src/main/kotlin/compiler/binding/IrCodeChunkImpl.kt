package compiler.binding

import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

internal class IrCodeChunkImpl(override val components: List<IrExecutable>) : IrCodeChunk
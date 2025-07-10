package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrUnreachableStatement

class IrUnreachableStatementImpl(
    val reason: String,
    override val isProvablyUnreachable: Boolean,
) : IrUnreachableStatement
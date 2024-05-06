package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue

class IrCreateStrongReferenceStatementImpl(
    override val reference: IrCreateTemporaryValue,
) : IrCreateStrongReferenceStatement
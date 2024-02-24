package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDropReferenceStatement

class IrDropReferenceStatementImpl(
    override val reference: IrCreateTemporaryValue,
) : IrDropReferenceStatement
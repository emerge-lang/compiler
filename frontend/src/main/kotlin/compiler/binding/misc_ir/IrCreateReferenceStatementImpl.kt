package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue

class IrCreateReferenceStatementImpl(
    override val reference: IrCreateTemporaryValue,
) : IrCreateReferenceStatement
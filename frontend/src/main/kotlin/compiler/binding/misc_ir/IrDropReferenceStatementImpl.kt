package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDropReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class IrDropReferenceStatementImpl(
    override val reference: IrTemporaryValueReference,
) : IrDropReferenceStatement {
    constructor(t: IrCreateTemporaryValue) : this(IrTemporaryValueReferenceImpl(t))
}
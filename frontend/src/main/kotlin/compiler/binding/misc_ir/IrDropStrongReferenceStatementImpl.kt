package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDropStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

class IrDropStrongReferenceStatementImpl(
    override val reference: IrTemporaryValueReference,
) : IrDropStrongReferenceStatement {
    constructor(t: IrCreateTemporaryValue) : this(IrTemporaryValueReferenceImpl(t))
}
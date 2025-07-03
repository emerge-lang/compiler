package compiler.binding

import compiler.binding.context.DeferrableExecutable
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class DeferredLocalVariableGCRelease(
    val variable: BoundVariable,
) : DeferrableExecutable {
    override val span = variable.declaration.span
    override fun toBackendIrStatement(): IrExecutable {
        val valueTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(variable.backendIrDeclaration))
        return IrCodeChunkImpl(listOf(
            valueTemporary,
            IrDropStrongReferenceStatementImpl(valueTemporary),
        ))
    }
}
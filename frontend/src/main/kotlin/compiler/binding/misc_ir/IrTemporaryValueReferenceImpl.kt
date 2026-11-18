package compiler.binding.misc_ir

import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * @param typeOverride see [IrTemporaryValueReference.type]
 */
internal class IrTemporaryValueReferenceImpl(
    override val declaration: IrCreateTemporaryValue,
    private val typeOverride: IrType? = null,
) : IrTemporaryValueReference {
    override val type: IrType get() = typeOverride ?: declaration.type
}

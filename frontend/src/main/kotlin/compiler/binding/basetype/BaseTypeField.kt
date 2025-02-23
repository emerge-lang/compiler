package compiler.binding.basetype

import compiler.binding.type.BoundTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * Models raw memory space inside the allocation of an object. Can be used to hold the data for a
 * [BoundBaseTypeMemberVariable], but also for any other higher-level logic (e.g. [BoundMixinStatement]).
 *
 * _This comes with 0 warranty. NO semantics (such as guaranteed initialization) are enforced around [BaseTypeField]s._
 */
class BaseTypeField(
    val id: Int,
    val type: BoundTypeReference,
) {
    private val _backendIr by lazy { IrClassFieldImpl(id, type.toBackendIr()) }
    fun toBackendIr(): IrClass.Field = _backendIr

    override fun toString(): String {
        return "BaseTypeField(id=$id, type=$type)"
    }
}

private class IrClassFieldImpl(
    override val id: Int,
    override val type: IrType,
) : IrClass.Field
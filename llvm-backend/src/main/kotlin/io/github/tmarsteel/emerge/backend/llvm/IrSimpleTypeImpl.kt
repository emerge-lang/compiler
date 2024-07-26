package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.independentToString

class IrSimpleTypeImpl(
    override val baseType: IrBaseType,
    override val mutability: IrTypeMutability,
    override val isNullable: Boolean,
) : IrSimpleType {
    override fun asNullable(): IrSimpleType {
        return IrSimpleTypeImpl(baseType, mutability,true)
    }

    override fun toString(): String = independentToString()
}
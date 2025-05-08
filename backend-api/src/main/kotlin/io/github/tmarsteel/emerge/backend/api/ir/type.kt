package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrType {
    val isNullable: Boolean
    val mutability: IrTypeMutability

    fun asNullable(): IrType
}

interface IrSimpleType : IrType {
    val baseType: IrBaseType

    override fun asNullable(): IrSimpleType
}

interface IrParameterizedType : IrType {
    val simpleType: IrSimpleType
    val arguments: Map<String, Argument>

    override val mutability get() = simpleType.mutability
    override val isNullable get() = simpleType.isNullable

    override fun asNullable(): IrParameterizedType

    interface Argument {
        val variance: IrTypeVariance
        val type: IrType
    }
}

enum class IrTypeMutability {
    MUTABLE,
    IMMUTABLE,
    READONLY,
    EXCLUSIVE,
}

enum class IrTypeVariance {
    INVARIANT,
    IN,
    OUT,
    ;
}

interface IrGenericTypeReference : IrType {
    val parameter: IrBaseType.Parameter
    val effectiveBound: IrType

    override val mutability get() = effectiveBound.mutability
    override val isNullable get() = effectiveBound.isNullable
    override fun asNullable(): IrGenericTypeReference
}

interface IrIntersectionType : IrType {
    val components: List<IrType>
}
package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrType {
    val isNullable: Boolean
}

interface IrSimpleType : IrType {
    val baseType: IrBaseType
}

interface IrParameterizedType : IrType {
    val simpleType: IrSimpleType
    val arguments: Map<String, Argument>

    override val isNullable get() = simpleType.isNullable

    interface Argument {
        val variance: IrTypeVariance
        val type: IrType
    }
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

    override val isNullable get() = effectiveBound.isNullable
}
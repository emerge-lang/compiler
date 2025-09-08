package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrType {
    val isNullable: Boolean
    val mutability: IrTypeMutability

    fun asNullable(): IrType

    /**
     * If this type is already concrete (based on [IrSimpleType]), should return itself.
     * If this is a generic or composite type, should return a concrete type that is the/an upper bound to
     * the generic or compound type. This upper bound errs on the side of being less abstract for the sake of
     * making sure that the [concreteUpperBound]  is truly a superset of `this` type.
     */
    val concreteUpperBound: IrBaseType
}

interface IrSimpleType : IrType {
    val baseType: IrBaseType

    override fun asNullable(): IrSimpleType

    override val concreteUpperBound get()= baseType
}

interface IrParameterizedType : IrType {
    val simpleType: IrSimpleType
    val arguments: Map<String, Argument>

    override val mutability get() = simpleType.mutability
    override val isNullable get() = simpleType.isNullable

    override fun asNullable(): IrParameterizedType

    override val concreteUpperBound get()= simpleType.concreteUpperBound

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

    override val concreteUpperBound get()= effectiveBound.concreteUpperBound
}

interface IrIntersectionType : IrType {
    val components: List<IrType>
}
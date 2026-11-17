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
    OWN,
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

    /**
     * `null` if this is a plain reference to the type parameter: at runtime the type is exactly the type argument.
     * `true` for `T?` and `false` for `T!`: the nullability of the type argument is replaced at runtime.
     */
    val nullabilityOverride: Boolean?

    /**
     * `null` if this is a plain reference to the type parameter: at runtime the mutability is that of the type
     * argument. Otherwise, the mutability written on the reference (`mut T`): at runtime the type is the type
     * argument, of the mutability that both it and this ask for (`mut T` of a `read Foo` is a `mut Foo`, of a
     * `const Foo` it is an `own Foo`).
     */
    val givenMutability: IrTypeMutability?

    override val mutability get() = effectiveBound.mutability
    override val isNullable get() = effectiveBound.isNullable
    override fun asNullable(): IrGenericTypeReference
}

interface IrIntersectionType : IrType {
    val components: List<IrType>
}
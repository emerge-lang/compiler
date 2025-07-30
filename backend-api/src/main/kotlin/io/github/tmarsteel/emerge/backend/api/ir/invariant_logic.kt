/**
 * This file contains logic that must stay constant across frontends and/or backends, and thus is defined entirely
 * as extension methods.
 */
package io.github.tmarsteel.emerge.backend.api.ir

import kotlin.reflect.KClass

fun IrBaseType.independentEquals(other: IrBaseType): Boolean {
    if (this.canonicalName != other.canonicalName) return false

    return true
}

fun IrBaseType.Parameter.independentEquals(other: IrBaseType.Parameter): Boolean {
    if (!this.bound.independentEquals(other.bound)) return false
    if (this.name != other.name) return false

    return true
}

fun IrParameterizedType.Argument.independentEquals(other: IrParameterizedType.Argument): Boolean {
    if (this.variance != other.variance) return false
    if (!this.type.independentEquals(other.type)) return false

    return true
}

fun IrType.independentEquals(other: IrType): Boolean {
    if (this.isNullable != other.isNullable) return false
    if (this.mutability != other.mutability) return false

    return when (this) {
        is IrSimpleType -> other is IrSimpleType && this.baseType.independentEquals(other.baseType)
        is IrGenericTypeReference -> other is IrGenericTypeReference
                && this.parameter.independentEquals(other.parameter)
                && this.effectiveBound.independentEquals(other.effectiveBound)
        is IrParameterizedType -> other is IrParameterizedType
                && this.simpleType.independentEquals(other.simpleType)
                && this.arguments.independentEquals(other.arguments, String::equals, IrParameterizedType.Argument::independentEquals)
        is IrIntersectionType -> other is IrIntersectionType && this.components.size == other.components.size && this.components.asSequence().sortedWith(IrTypeComparator)
            .zip(other.components.asSequence().sortedWith(IrTypeComparator))
            .all { (a, b) -> a.independentEquals(b) }
    }
}

fun IrType.independentToString(): String {
    val mutabilityStr = when(mutability) {
        IrTypeMutability.IMMUTABLE -> "const"
        IrTypeMutability.READONLY -> "read"
        IrTypeMutability.MUTABLE -> "mut"
        IrTypeMutability.EXCLUSIVE -> "exclusive"
    }
    return when (this) {
        is IrSimpleType -> "$mutabilityStr ${baseType.canonicalName}${if (isNullable) "?" else ""}"
        is IrParameterizedType -> this.arguments.entries.joinToString(
            prefix = "$mutabilityStr ${simpleType.baseType.canonicalName}<",
            transform = { (argName, arg) ->
                val varianceStr = when (arg.variance) {
                    IrTypeVariance.IN -> "in "
                    IrTypeVariance.OUT -> "out "
                    IrTypeVariance.INVARIANT -> ""
                }
                "$argName = ${varianceStr}${arg.type.independentToString()}"
            },
            separator = ", ",
            postfix = ">${if (isNullable) "?" else ""}"
        )
        is IrGenericTypeReference -> {
            "${this.parameter.name} : ${this.effectiveBound.independentToString()}"
        }
        is IrIntersectionType -> components.joinToString(separator = " & ")
    }
}

private fun <K, V> Map<K, V>.independentEquals(other: Map<K, V>, keyEquality: (K, K) -> Boolean, valueEquality: (V, V) -> Boolean): Boolean {
    if (this.size != other.size) return false

    for ((selfKey, selfValue) in this) {
        val otherEntry = other.entries.firstOrNull { (key, _) -> keyEquality(key, selfKey) }
            ?: return false
        if (!valueEquality(selfValue, otherEntry.value)) {
            return false
        }
    }

    return true
}

/**
 * Brings [IrType]s into a canonical order, which is important to compare compound types (e.g. [IrIntersectionType])
 * for equality.
 */
private object IrTypeComparator : Comparator<IrType> {
    private val irTypeClassOrder = listOf<KClass<out IrType>>(
        IrSimpleType::class,
        IrGenericTypeReference::class,
        IrParameterizedType::class,
        IrIntersectionType::class,
    )

    private val typeByClassComparator: Comparator<IrType> = compareBy { irType ->
        irTypeClassOrder
            .mapIndexedNotNull { index, clazz ->
                if (clazz.isInstance(irType)) index else null
            }
            .single()
    }

    private val typeArgumentComparator = compareBy<IrParameterizedType.Argument> { it.variance }
        .thenBy(this) { it.type }

    private fun compareSubtypeSpecific(o1: IrType, o2: IrType): Int {
        return when (o1) {
            is IrSimpleType -> {
                check(o2 is IrSimpleType) { "assured by kclass-comparator" }
                o1.baseType.canonicalName.compareTo(o2.baseType.canonicalName)
            }
            is IrGenericTypeReference -> {
                check(o2 is IrGenericTypeReference)
                o1.parameter.name.compareTo(o2.parameter.name)
            }
            is IrParameterizedType -> {
                check(o2 is IrParameterizedType)
                val bySimple = compareSubtypeSpecific(o1.simpleType, o2.simpleType)
                if (bySimple != 0) {
                    return bySimple
                }

                val byArguments = o1.arguments.entries
                    .asSequence()
                    .sortedBy { it.key }
                    .map { (o1argName, o1argValue) ->
                        val o2argValue = o2.arguments[o1argName]!!
                        typeArgumentComparator.compare(o1argValue, o2argValue)
                    }
                    .filter { it != 0 }
                    .firstOrNull() ?: 0

                byArguments
            }
            is IrIntersectionType -> {
                check(o2 is IrIntersectionType)
                o1.components.asSequence().sortedWith(this)
                    .zip(o2.components.asSequence().sortedWith(this))
                    .map { (o1c, o2c) -> compare(o1c, o2c) }
                    .filter { it != 0 }
                    .firstOrNull()
                    ?.let { return it }
                    ?: o1.components.size.compareTo(o2.components.size) // at this point, the type with more components is more specific
            }
        }
    }

    private val delegate = typeByClassComparator
        .thenComparing(this::compareSubtypeSpecific)
        .thenBy { it.isNullable }
        .thenBy { it.mutability }

    override fun compare(o1: IrType, o2: IrType): Int = delegate.compare(o1, o2)
}
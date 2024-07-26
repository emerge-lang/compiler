/**
 * This file contains logic that must stay constant across frontends and/or backends, and thus is defined entirely
 * as extension methods.
 */
package io.github.tmarsteel.emerge.backend.api.ir

fun IrBaseType.independentEquals(other: IrBaseType): Boolean {
    if (this.canonicalName != other.canonicalName) return false

    return true
}

fun IrBaseType.Parameter.independentEquals(other: IrBaseType.Parameter): Boolean {
    if (this.variance != other.variance) return false
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

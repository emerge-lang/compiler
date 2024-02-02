package io.github.tmarsteel.emerge.backend.llvm.dsl

import kotlin.reflect.KProperty

fun <T : LlvmType> cachedType(builder: LlvmContext.() -> T) : CachedTypeDelegate<T> {
    return CachedTypeDelegate(builder)
}

class CachedTypeDelegate<T : LlvmType>(
    private val builder: LlvmContext.() -> T
) {
    operator fun getValue(thisRef: LlvmContext, property: KProperty<*>): T {
        return thisRef.cachedType(property.name, builder)
    }
}
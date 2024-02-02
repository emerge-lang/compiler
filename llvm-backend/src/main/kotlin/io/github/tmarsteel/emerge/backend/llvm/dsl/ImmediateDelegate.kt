package io.github.tmarsteel.emerge.backend.llvm.dsl

import kotlin.reflect.KProperty

/**
 * A delegate for the sole purpose of having a delegate interface. It just returns a predefined value.
 */
class ImmediateDelegate<in Receiver, out T>(
    val value: T
) {
    operator fun getValue(thisRef: Receiver, prop: KProperty<*>): T = value
}
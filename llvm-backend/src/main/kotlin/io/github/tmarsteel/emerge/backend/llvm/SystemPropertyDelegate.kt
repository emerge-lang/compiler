package io.github.tmarsteel.emerge.backend.llvm

import kotlin.reflect.KProperty

class SystemPropertyDelegate<T>(
    val name: String,
    val transform: (String) -> T,
) {
    operator fun getValue(thisRef: Any?, property: KProperty<*>): T {
        val value = System.getProperty(name)
            ?: throw IllegalStateException("Required system property $name is not set")

        return try {
            transform(value)
        } catch (ex: IllegalArgumentException) {
            throw IllegalArgumentException("System property $name is invalid: ${ex.message}", ex)
        }
    }

    companion object {
        fun <T> systemProperty(name: String, transform: (String) -> T) = SystemPropertyDelegate<T>(name, transform)
    }
}
package io.github.tmarsteel.emerge.backend.api

class DotName(val components: List<String>) {
    init {
        require(components.isNotEmpty())
    }

    override fun toString() = components.joinToString(separator = ".")

    fun containsOrEquals(other: List<String>): Boolean {
        if (components.size > other.size) {
            return false
        }

        return components.zip(other).all { (a, b) -> a == b }
    }

    fun containsOrEquals(other: DotName): Boolean {
        return containsOrEquals(other.components)
    }

    operator fun plus(other: String): DotName {
        return DotName(components + other)
    }

    val last: String get() = components.last()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as DotName

        return components == other.components
    }

    override fun hashCode(): Int {
        return components.hashCode()
    }
}
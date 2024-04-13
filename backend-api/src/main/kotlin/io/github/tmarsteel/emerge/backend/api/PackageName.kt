package io.github.tmarsteel.emerge.backend.api

/**
 * Name of a package or a module
 */
class PackageName(val components: List<String>) {
    init {
        require(components.isNotEmpty())
        require(components.none { '.' in it })
    }

    val last: String get() = components.last()

    fun containsOrEquals(other: PackageName): Boolean {
        return containsOrEquals(other.components)
    }

    operator fun plus(other: String): PackageName {
        return PackageName(components + other)
    }

    override fun toString() = components.joinToString(separator = ".")

    private fun containsOrEquals(other: List<String>): Boolean {
        if (components.size > other.size) {
            return false
        }

        return components.zip(other).all { (a, b) -> a == b }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as PackageName

        return components == other.components
    }

    override fun hashCode(): Int {
        return components.hashCode()
    }
}
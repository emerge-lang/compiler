package compiler

class PackageName(val components: List<String>) {

    override fun toString() = components.joinToString(separator = ".")

    fun containsOrEquals(other: List<String>): Boolean {
        if (components.size > other.size) {
            return false
        }

        return components.zip(other).all { (a, b) -> a == b }
    }

    fun containsOrEquals(other: PackageName): Boolean {
        return containsOrEquals(other.components)
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
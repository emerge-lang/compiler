package io.github.tmarsteel.emerge.backend.api

/**
 * A name that can unambiguously point out any
 * * type (class or interface)
 * * function
 * * member function
 * * global variable
 * * member variable
 * (not accounting for code versioning). This is used to uniquely identify
 * things (e.g. to a linker), but also to the user if need be.
 *
 * It uses symbols disallowed from regular [IdentifierToken]s to have a clear,
 * impenetrable boundary between user-specified parts.
 *
 * Does not encode
 * * function parameter types and return types
 * * variable types
 * * type parameters or arguments
 */
sealed interface CanonicalElementName {

    abstract override fun toString(): String

    class Package(val components: List<String>) : CanonicalElementName {
        init {
            require(components.isNotEmpty())
            require(components.none { '.' in it })
        }

        val last: String get() = components.last()

        fun containsOrEquals(other: Package): Boolean {
            return containsOrEquals(other.components)
        }

        operator fun plus(other: String): Package {
            return Package(components + other)
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

            other as Package

            return components == other.components
        }

        override fun hashCode(): Int {
            return components.hashCode()
        }
    }

    class BaseType(
        val packageName: Package,
        val simpleName: String
    ) : CanonicalElementName {
        override fun toString() = "${packageName}.${simpleName}"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is BaseType) return false

            if (packageName != other.packageName) return false
            if (simpleName != other.simpleName) return false

            return true
        }

        override fun hashCode(): Int {
            var result = packageName.hashCode()
            result = 31 * result + simpleName.hashCode()
            return result
        }
    }

    class Function(
        val parent: CanonicalElementName,
        val simpleName: String
    ) : CanonicalElementName {
        override fun toString() = when (parent) {
            is Package -> "$parent.$simpleName"
            else -> "$parent::$simpleName"
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Function) return false

            if (parent != other.parent) return false
            if (simpleName != other.simpleName) return false

            return true
        }

        override fun hashCode(): Int {
            var result = parent.hashCode()
            result = 31 * result + simpleName.hashCode()
            return result
        }
    }

    class Global(
        val parent: Package,
        val simpleName: String
    ) : CanonicalElementName {
        override fun toString() = "$parent.$simpleName"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Global) return false

            if (parent != other.parent) return false
            if (simpleName != other.simpleName) return false

            return true
        }

        override fun hashCode(): Int {
            var result = parent.hashCode()
            result = 31 * result + simpleName.hashCode()
            return result
        }
    }
}
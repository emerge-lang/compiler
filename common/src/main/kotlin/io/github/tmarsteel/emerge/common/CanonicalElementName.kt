package io.github.tmarsteel.emerge.common

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

    class Package(val components: List<String>) : CanonicalElementName, Comparable<Package> {
        init {
            require(components.isNotEmpty())
            require(components.none { '.' in it })
        }

        val last: String get() = components.last()

        /**
         * Whether `this` is the same package as [other], or, is a in the same hierarchy, and higher up.
         * E.g. `emerge.core` containsOrEquals `emerge.core.reflection`.
         */
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

        override fun compareTo(other: Package): Int {
            this.components.asSequence()
                .zip(other.components.asSequence())
                .map { (selfComponent, otherComponent) ->
                    selfComponent.compareTo(otherComponent)
                }
                .filter { it != 0 }
                .firstOrNull()
                ?.let { return it }

            // at this point, the common prefix is identical
            return this.components.size.compareTo(other.components.size)
        }
    }

    class BaseType(
        val packageName: Package,
        val simpleName: String
    ) : CanonicalElementName, Comparable<BaseType> {
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

        override fun compareTo(other: BaseType): Int {
            val byPackage = this.packageName.compareTo(other.packageName)
            if (byPackage != 0) {
                return byPackage
            }

            return simpleName.compareTo(other.simpleName)
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
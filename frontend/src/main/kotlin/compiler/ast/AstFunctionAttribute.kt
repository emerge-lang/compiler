package compiler.ast

import compiler.lexer.IdentifierToken
import compiler.lexer.Token

/**
 * All subclasses define [Any.equals] and [Any.hashCode] in terms of semantics, source location from AST are not
 * considered.
 */
sealed class AstFunctionAttribute(
    val attributeName: Token,
) {
    open val impliesNoBody: Boolean = false
    val sourceLocation = attributeName.sourceLocation

    class Visibility(val value: Value, nameToken: Token) : AstFunctionAttribute(nameToken) {
        sealed interface Value {
            object Private : Value
            object Protected : Value
            object Internal : Value
            class Qualified(pkg: ASTPackageName) : Value
            object Exported : Value
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Visibility) return false

            if (value != other.value) return false

            return true
        }

        override fun hashCode(): Int {
            return value.hashCode()
        }
    }

    /**
     * This function is eligible to override syntactic operators, e.g. `*`
     */
    class Operator(nameToken: Token) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Operator) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    /**
     * The body of the function is provided by the backend. Used for target-specific functions, usually
     * the smallest of building blocks (e.g. `Int.opPlus(Int)`)
     */
    class Intrinsic(nameToken: Token) : AstFunctionAttribute(nameToken) {
        override val impliesNoBody = true

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Operator) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    class External(nameToken: Token, val ffiName: IdentifierToken) : AstFunctionAttribute(nameToken) {
        override val impliesNoBody = true

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is External) return false

            if (ffiName != other.ffiName) return false

            return true
        }

        override fun hashCode(): Int {
            return ffiName.hashCode()
        }
    }

    /**
     * TODO: yeet?
     */
    class Nothrow(nameToken: Token) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Operator) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    class EffectCategory(val value: Category, nameToken: Token) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is EffectCategory) return false

            if (value != other.value) return false

            return true
        }

        override fun hashCode(): Int {
            return value.hashCode()
        }

        enum class Category {
            MODIFYING,
            READONLY,
            PURE
        }
    }
}


package compiler.ast

import compiler.binding.BoundFunction
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken

/**
 * All subclasses define [Any.equals] and [Any.hashCode] in terms of semantics, source location from AST are not
 * considered.
 */
sealed class AstFunctionAttribute(
    val attributeName: KeywordToken,
) {
    open val impliesNoBody: Boolean = false
    val sourceLocation = attributeName.span

    /**
     * This function is eligible to override syntactic operators, e.g. `*`
     */
    class Operator(nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
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
    class Intrinsic(nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
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

    class External(nameToken: KeywordToken, val ffiName: IdentifierToken) : AstFunctionAttribute(nameToken) {
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

    class Nothrow(nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Nothrow) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    class Override(nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Override) return false
            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    class EffectCategory(val value: BoundFunction.Purity, nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is EffectCategory) return false

            if (value != other.value) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + value.hashCode()
            return result
        }
    }

    class Accessor(val mode: Mode, nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Accessor) return false

            if (mode != other.mode) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + mode.hashCode()
            return result
        }

        // TODO: rename to Kind
        enum class Mode {
            READ,
            WRITE,
            ;
        }
    }
}


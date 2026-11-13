package compiler.ast

import compiler.ast.expression.StringLiteralExpression
import compiler.binding.AccessorKind
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

    /**
     * `external(C)` or `external(C, "symbol")`
     * @param ffiName the calling convention, e.g. `C`
     * @param symbolName the name of the foreign symbol the function binds to; if absent, the name of the function.
     * Needed e.g. for C symbols that start with `__`, which emerge reserves for the compiler.
     */
    class External(
        nameToken: KeywordToken,
        val ffiName: IdentifierToken,
        val symbolName: StringLiteralExpression? = null,
    ) : AstFunctionAttribute(nameToken) {
        override val impliesNoBody = true

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is External) return false

            if (ffiName != other.ffiName) return false
            if (symbolName?.content?.content != other.symbolName?.content?.content) return false

            return true
        }

        override fun hashCode(): Int {
            return ffiName.hashCode() * 31 + (symbolName?.content?.content?.hashCode() ?: 0)
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

    class Accessor(val kind: AccessorKind, nameToken: KeywordToken) : AstFunctionAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Accessor) return false

            if (kind != other.kind) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + kind.hashCode()
            return result
        }
    }
}


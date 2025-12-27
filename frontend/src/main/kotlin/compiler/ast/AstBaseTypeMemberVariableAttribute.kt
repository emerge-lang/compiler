package compiler.ast

import compiler.lexer.KeywordToken

sealed class AstBaseTypeMemberVariableAttribute(
    val attributeName: KeywordToken,
) {
    fun conflictsWith(other: AstBaseTypeMemberVariableAttribute) = this.javaClass == other.javaClass && attributeName.keyword != other.attributeName.keyword

    class Ownership(nameToken: KeywordToken) : AstBaseTypeMemberVariableAttribute(nameToken) {
        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Ownership) return false

            if (attributeName.keyword != other.attributeName.keyword) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + attributeName.hashCode()
            return result
        }

        /** TODO: unused? */
        private enum class OwnershipKind { OWNED, REFERENCED }
    }
}
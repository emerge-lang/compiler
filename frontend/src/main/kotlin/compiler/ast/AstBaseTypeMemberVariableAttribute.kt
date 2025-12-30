package compiler.ast

import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken

sealed class AstBaseTypeMemberVariableAttribute(
    val attributeName: KeywordToken,
) {
    fun conflictsWith(other: AstBaseTypeMemberVariableAttribute) = this.javaClass == other.javaClass && attributeName.keyword != other.attributeName.keyword

    class Ownership(nameToken: KeywordToken) : AstBaseTypeMemberVariableAttribute(nameToken) {
        val ownership: BoundBaseTypeMemberVariable.Ownership = when (nameToken.keyword) {
            Keyword.REF -> BoundBaseTypeMemberVariable.Ownership.REFERENCED
            Keyword.OWN -> BoundBaseTypeMemberVariable.Ownership.OWNED
            else -> error("invalid ownership keyword at ${nameToken.span}")
        }

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
    }
}
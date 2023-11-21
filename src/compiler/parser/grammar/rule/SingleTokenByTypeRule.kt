package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.lexer.TokenType

class SingleTokenByTypeRule(private val type: TokenType) : SingleTokenRule(ByTypeExpectedToken(type)) {
    override val descriptionOfAMatchingThing = type.name
    override fun matchAndPostprocess(token: Token) = token.takeIf { it.type == type }

    data class ByTypeExpectedToken(val type: TokenType) : ExpectedToken {
        override fun couldMatchSameTokenAs(other: ExpectedToken): Boolean {
            if (other is ByTypeExpectedToken && other.type == this.type) {
                return true
            }

            if (other is SingleTokenByEqualityRule.ByEqualityExpectedToken && other.expected.type == type) {
                return true
            }

            if (other is IdentifierRule.IdentifierExpectedToken) {
                if (type == TokenType.IDENTIFIER) {
                    return true
                }
                if (type == TokenType.OPERATOR && other.acceptedOperators.isNotEmpty()) {
                    return true
                }
                if (type == TokenType.KEYWORD && other.acceptedKeywords.isNotEmpty()) {
                    return true
                }
            }

            return false
        }
    }
}
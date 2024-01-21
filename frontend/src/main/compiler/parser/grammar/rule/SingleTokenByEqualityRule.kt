package compiler.parser.grammar.rule

import compiler.lexer.KeywordToken
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.lexer.TokenType

class SingleTokenByEqualityRule(private val expected: Token) : SingleTokenRule(ByEqualityExpectedToken(expected)) {
    override val descriptionOfAMatchingThing = expected.toStringWithoutLocation()
    override fun matchAndPostprocess(token: Token) = token.takeIf { it == expected }

    data class ByEqualityExpectedToken(val expected: Token) : ExpectedToken {
        override fun couldMatchSameTokenAs(other: ExpectedToken): Boolean {
            if (other is ByEqualityExpectedToken && other.expected == this.expected) {
                return true
            }

            if (other is SingleTokenByTypeRule.ByTypeExpectedToken && other.type == expected.type) {
                return true
            }

            if (other is IdentifierRule.IdentifierExpectedToken) {
                if (expected.type == TokenType.IDENTIFIER) {
                    return true
                }

                if (expected is KeywordToken && expected.keyword in other.acceptedKeywords) {
                    return true
                }

                if (expected is OperatorToken && expected.operator in other.acceptedOperators) {
                    return true
                }
            }

            return false
        }
    }
}
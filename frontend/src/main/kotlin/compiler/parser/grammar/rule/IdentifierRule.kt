package compiler.parser.grammar.rule

import compiler.lexer.*

class IdentifierRule(
    private val acceptedOperators: Set<Operator>,
    private val acceptedKeywords: Set<Keyword>,
) : SingleTokenRule(
    IdentifierExpectedToken(acceptedOperators, acceptedKeywords),
) {
    override val descriptionOfAMatchingThing: String by lazy {
        var out = "any identifier"
        if (acceptedOperators.isNotEmpty()) {
            out += ", any of these operators " + acceptedOperators.joinToString(", ")
        }
        if (acceptedKeywords.isNotEmpty()) {
            out += ", any of these keywords " + acceptedKeywords.joinToString(", ")
        }

        out
    }

    override fun matchAndPostprocess(token: Token): Token? = when (token) {
        is IdentifierToken -> token
        is OperatorToken -> if (token.operator in acceptedOperators) {
            IdentifierToken(token.operator.text, token.sourceLocation)
        } else null
        is KeywordToken -> if (token.keyword in acceptedKeywords) {
            IdentifierToken(token.keyword.text, token.sourceLocation)
        } else null
        else -> null
    }

    data class IdentifierExpectedToken(
        val acceptedOperators: Set<Operator>,
        val acceptedKeywords: Set<Keyword>,
    ) : ExpectedToken {
        override fun couldMatchSameTokenAs(other: ExpectedToken): Boolean {
            if (other is IdentifierExpectedToken) {
                return true
            }

            if (other is SingleTokenByTypeRule.ByTypeExpectedToken && other.type == TokenType.IDENTIFIER) {
                return true
            }

            if (other is SingleTokenByEqualityRule.ByEqualityExpectedToken && other.expected.type == TokenType.IDENTIFIER) {
                return true
            }

            return false
        }
    }
}
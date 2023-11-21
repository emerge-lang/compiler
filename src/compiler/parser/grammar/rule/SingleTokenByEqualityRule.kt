package compiler.parser.grammar.rule

import compiler.lexer.Token

class SingleTokenByEqualityRule(private val expected: Token) : SingleTokenRule(ByEqualityExpectedToken(expected)) {
    override val descriptionOfAMatchingThing = expected.toStringWithoutLocation()
    override fun matchAndPostprocess(token: Token) = token.takeIf { it == expected }

    private data class ByEqualityExpectedToken(private val token: Token) : ExpectedToken
}
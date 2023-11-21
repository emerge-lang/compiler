package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.lexer.TokenType
import compiler.parser.TokenSequence
import compiler.reportings.Reporting

class SingleTokenByTypeRule(private val type: TokenType) : SingleTokenRule(ByTypeExpectedToken(type)) {
    override val descriptionOfAMatchingThing = type.name
    override fun matchAndPostprocess(token: Token) = token.takeIf { it.type == type }

    private data class ByTypeExpectedToken(private val type: TokenType) : ExpectedToken
}
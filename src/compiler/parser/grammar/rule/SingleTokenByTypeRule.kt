package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.lexer.TokenType
import compiler.parser.TokenSequence
import compiler.reportings.Reporting

class SingleTokenByTypeRule(private val type: TokenType) : Rule<Token> {
    override val descriptionOfAMatchingThing: String get() = type.name

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Token> {
        if (!input.hasNext()) {
            return RuleMatchingResult(
                true,
                null,
                setOf(
                    Reporting.unexpectedEOI(type.toString(), input.currentSourceLocation)
                )
            )
        }

        input.mark()

        val token = input.next()!!
        if (token.type == type) {
            input.commit()
            return RuleMatchingResult(
                false,
                token,
                emptySet()
            )
        }

        input.rollback()
        return RuleMatchingResult(
            true,
            null,
            setOf(Reporting.parsingError("Expected $type but found $token", token.sourceLocation))
        )
    }

    override val minimalMatchingSequence = sequenceOf(sequenceOf(ByTypeExpectedToken(type) as ExpectedToken))

    private data class ByTypeExpectedToken(private val type: TokenType) : ExpectedToken {
        override fun markAsRemovingAmbiguity(inContext: Any) {

        }
    }
}
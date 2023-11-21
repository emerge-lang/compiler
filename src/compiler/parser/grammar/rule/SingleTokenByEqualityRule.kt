package compiler.parser.grammar.rule

import compiler.lexer.Token
import compiler.parser.TokenSequence
import compiler.reportings.MissingTokenReporting
import compiler.reportings.TokenMismatchReporting

class SingleTokenByEqualityRule(private val equalTo: Token) : Rule<Token> {
    override val explicitName = null
    override val descriptionOfAMatchingThing: String get() = equalTo.toStringWithoutLocation()

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Token> {
        if (!input.hasNext()) {
            return RuleMatchingResult(
                true,
                null,
                setOf(
                    MissingTokenReporting(equalTo, input.currentSourceLocation)
                )
            )
        }

        input.mark()

        val token = input.next()!!
        if (token == equalTo) {
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
            setOf(TokenMismatchReporting(equalTo, token))
        )
    }

    override val minimalMatchingSequence = sequenceOf(sequenceOf(ByEqualityExpectedToken(equalTo) as ExpectedToken))

    private data class ByEqualityExpectedToken(private val token: Token) : ExpectedToken {
        override fun markAsRemovingAmbiguity(inContext: Any) {

        }
    }
}
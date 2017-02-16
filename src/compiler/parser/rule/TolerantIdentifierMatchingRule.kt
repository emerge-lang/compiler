package compiler.parser.rule

import compiler.lexer.*
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.TokenSequence

/**
 * Matches [IdentifierToken]s, as well as predefined types of [OperatorToken] and [KeywordToken]. This is to be used
 * in places where keywords and operators are to be treated as if they were simple identifiers.<br>
 * Converts these [OperatorToken]s and[KeywordToken]s into equivalent [IdentifierTokens] pointing to the same [SourceLocation].
 *
 * TODO: maybe refactor into a more general rule that can converty anything into an identifier using a given (Token) -> IdentifierToken? mapper
 */
class TolerantIdentifierMatchingRule(
    val acceptedOperators: Collection<Operator>,
    val acceptedKeywords: Collection<Keyword>
) : Rule<IdentifierToken> {
    override val descriptionOfAMatchingThing: String
        get() {
            var out = "any identifier"
            if (acceptedOperators.isNotEmpty()) {
                out += ", any of these operators " + acceptedOperators.joinToString(", ")
            }
            if (acceptedKeywords.isNotEmpty()) {
                out += ", any of these keywords " + acceptedKeywords.joinToString(", ")
            }

            return out
        }

    override fun tryMatch(input: TokenSequence): MatchingResult<IdentifierToken> {
        if (!input.hasNext()) {
            return MatchingResult(
                ResultCertainty.DEFINITIVE,
                null,
                setOf(Reporting.unexpectedEOI(descriptionOfAMatchingThing, input.currentSourceLocation))
            )
        }

        input.mark()

        val token = input.next()!!

        if (token is IdentifierToken) {
            // awww, nice :))
            return MatchingResult(
                ResultCertainty.DEFINITIVE,
                token,
                emptySet()
            )
        } else if (token is OperatorToken && token.operator in acceptedOperators) {
            return MatchingResult(
                ResultCertainty.DEFINITIVE,
                IdentifierToken(token.operator.text, token.sourceLocation),
                emptySet()
            )
        } else if (token is KeywordToken && token.keyword in acceptedKeywords) {
            return MatchingResult(
                ResultCertainty.DEFINITIVE,
                IdentifierToken(token.sourceText, token.sourceLocation),
                emptySet()
            )
        }

        // none matched => error
        return MatchingResult(
            ResultCertainty.DEFINITIVE,
            null,
            setOf(Reporting.error("Unexpected $token, expecting $descriptionOfAMatchingThing", token))
        )
    }
}
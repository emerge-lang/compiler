package compiler.parser.grammar.rule

import compiler.lexer.*
import compiler.parser.TokenSequence
import compiler.reportings.Reporting

class IdentifierRule(
    private val acceptedOperators: Collection<Operator>,
    private val acceptedKeywords: Collection<Keyword>,
) : Rule<IdentifierToken> {
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

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<IdentifierToken> {
        if (!input.hasNext()) {
            return RuleMatchingResult(
                false,
                null,
                setOf(Reporting.unexpectedEOI(descriptionOfAMatchingThing, input.currentSourceLocation))
            )
        }

        input.mark()
        val token = input.next()!!

        if (token is IdentifierToken) {
            input.commit()
            return RuleMatchingResult(
                false,
                token,
                emptySet()
            )
        } else if (token is OperatorToken && token.operator in acceptedOperators) {
            input.commit()
            return RuleMatchingResult(
                false,
                IdentifierToken(token.operator.text, token.sourceLocation),
                emptySet()
            )
        } else if (token is KeywordToken && token.keyword in acceptedKeywords) {
            input.commit()
            return RuleMatchingResult(
                false,
                IdentifierToken(token.sourceText, token.sourceLocation),
                emptySet()
            )
        }

        // none matched => error
        input.rollback()
        return RuleMatchingResult(
            false,
            null,
            setOf(Reporting.parsingError("Unexpected ${token.toStringWithoutLocation()}, expecting $descriptionOfAMatchingThing", token.sourceLocation))
        )
    }
}
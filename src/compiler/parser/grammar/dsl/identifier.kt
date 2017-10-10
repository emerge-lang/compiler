package compiler.parser.grammar.dsl

import compiler.lexer.*
import compiler.matching.ResultCertainty
import compiler.parser.Reporting
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl

/**
 * Matches [IdentifierToken]s, as well as predefined types of [OperatorToken] and [KeywordToken]. This is to be used
 * in places where keywords and operators are to be treated as if they were simple identifiers.<br>
 * Converts these [OperatorToken]s and[KeywordToken]s into equivalent [IdentifierTokens] pointing to the same [SourceLocation].
 *
 * TODO: maybe refactor into a more general rule that can convert anything into an identifier using a given (Token) -> IdentifierToken? mapper
 */
internal fun tryMatchIdentifier(input: TokenSequence, acceptedOperators: Collection<Operator>,
                                acceptedKeywords: Collection<Keyword>): RuleMatchingResult<IdentifierToken> {
    if (!input.hasNext()) {
        return RuleMatchingResultImpl(
            ResultCertainty.DEFINITIVE,
            null,
            setOf(Reporting.unexpectedEOI(describeIdentifier(acceptedOperators, acceptedKeywords), input.currentSourceLocation))
        )
    }

    input.mark()

    val token = input.next()!!

    if (token is IdentifierToken) {
        return RuleMatchingResultImpl(
            ResultCertainty.DEFINITIVE,
            token,
            emptySet()
        )
    } else if (token is OperatorToken && token.operator in acceptedOperators) {
        return RuleMatchingResultImpl(
            ResultCertainty.DEFINITIVE,
            IdentifierToken(token.operator.text, token.sourceLocation),
            emptySet()
        )
    } else if (token is KeywordToken && token.keyword in acceptedKeywords) {
        return RuleMatchingResultImpl(
            ResultCertainty.DEFINITIVE,
            IdentifierToken(token.sourceText, token.sourceLocation),
            emptySet()
        )
    }

    // none matched => error
    return RuleMatchingResultImpl(
        ResultCertainty.DEFINITIVE,
        null,
        setOf(Reporting.error("Unexpected ${token.toStringWithoutLocation()}, expecting ${describeIdentifier(acceptedOperators, acceptedKeywords)}", token))
    )
}

internal fun describeIdentifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>): String {
    var out = "any identifier"
    if (acceptedOperators.isNotEmpty()) {
        out += ", any of these operators " + acceptedOperators.joinToString(", ")
    }
    if (acceptedKeywords.isNotEmpty()) {
        out += ", any of these keywords " + acceptedKeywords.joinToString(", ")
    }

    return out
}
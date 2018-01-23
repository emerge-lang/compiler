/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.parser.grammar.dsl

import compiler.lexer.*
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.reportings.Reporting

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
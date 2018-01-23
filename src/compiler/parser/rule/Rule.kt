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

package compiler.parser.rule

import compiler.lexer.Token
import compiler.lexer.TokenType
import compiler.matching.Matcher
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.reportings.MissingTokenReporting
import compiler.reportings.Reporting
import compiler.reportings.TokenMismatchReporting

interface Rule<T> : Matcher<TokenSequence,T, Reporting> {
    companion object {
        fun singleton(equalTo: Token, mismatchCertainty: ResultCertainty = ResultCertainty.NOT_RECOGNIZED): Rule<Token> = object : Rule<Token> {
            override val descriptionOfAMatchingThing: String
                get() = equalTo.toString()

            override fun tryMatch(input: TokenSequence): RuleMatchingResult<Token> {
                if (!input.hasNext()) {
                    return RuleMatchingResultImpl(
                        mismatchCertainty,
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
                    return RuleMatchingResultImpl(
                        ResultCertainty.DEFINITIVE,
                        token,
                        emptySet()
                    )
                }
                else {
                    input.rollback()
                    return RuleMatchingResultImpl(
                        mismatchCertainty,
                        null,
                        setOf(
                            TokenMismatchReporting(equalTo, token)
                        )
                    )
                }
            }
        }

        fun singletonOfType(type: TokenType): Rule<Token> = object : Rule<Token> {
            override val descriptionOfAMatchingThing: String
                get() = type.name

            override fun tryMatch(input: TokenSequence): RuleMatchingResult<Token> {
                if (!input.hasNext()) {
                    return RuleMatchingResultImpl(
                        ResultCertainty.NOT_RECOGNIZED,
                        null,
                        setOf(
                            Reporting.error("Expected token of type $type, found nothing", input.currentSourceLocation)
                        )
                    )
                }

                input.mark()

                val token = input.next()!!
                if (token.type == type) {
                    input.commit()
                    return RuleMatchingResultImpl(
                        ResultCertainty.OPTIMISTIC,
                        token,
                        emptySet()
                    )
                }
                else {
                    input.rollback()
                    return RuleMatchingResultImpl(
                        ResultCertainty.NOT_RECOGNIZED,
                        null,
                        setOf(
                                Reporting.error("Expected token of type $type, found $token", token)
                        )
                    )
                }
            }
        }
    }

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<T>
}
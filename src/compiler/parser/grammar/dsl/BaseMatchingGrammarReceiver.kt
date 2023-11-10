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
import compiler.parser.Rule
import compiler.parser.RuleMatchingResult
import compiler.parser.TokenSequence
import compiler.reportings.MissingTokenReporting
import compiler.reportings.Reporting
import compiler.reportings.TokenMismatchReporting

internal abstract class BaseMatchingGrammarReceiver(
    private val context: Any,
    internal val input: TokenSequence,
) : GrammarReceiver {
    /**
     * Is called by all other methods as soon as there is a matching result
     */
    protected abstract fun handleResult(result: RuleMatchingResult<*>)

    override fun tokenEqualTo(equalTo: Token) {
        if (!input.hasNext()) {
            handleResult(RuleMatchingResult(
                true,
                null,
                setOf(
                    MissingTokenReporting(equalTo, input.currentSourceLocation)
                )
            ))
            return
        }

        input.mark()

        val token = input.next()!!
        if (token == equalTo) {
            input.commit()
            handleResult(RuleMatchingResult(
                false,
                token,
                emptySet()
            ))
            return
        }

        input.rollback()
        handleResult(RuleMatchingResult(
            true,
            null,
            setOf(
                TokenMismatchReporting(equalTo, token)
            )
        ))
    }

    override fun tokenOfType(type: TokenType) {
        if (!input.hasNext()) {
            handleResult(RuleMatchingResult(
                true,
                null,
                setOf(
                    Reporting.unexpectedEOI(type.toString(), input.currentSourceLocation)
                )
            ))
            return
        }

        input.mark()

        val token = input.next()!!
        if (token.type == type) {
            input.commit()
            handleResult(RuleMatchingResult(
                false,
                token,
                emptySet()
            ))
            return
        }

        input.rollback()
        handleResult(RuleMatchingResult(
            true,
            null,
            setOf(Reporting.parsingError("Expected $type but found $token", token.sourceLocation))
        ))
    }

    override fun ref(rule: Rule<*>) {
        // this branch is for testing only
        if (input.peek() is NestedRuleMockingToken) {
            handleResult(
                RuleMatchingResult(
                    false,
                    (input.next()!! as NestedRuleMockingToken).replacement,
                    emptySet(),
                )
            )
        } else {
            handleResult(rule.tryMatch(context, input))
        }
    }

    override fun sequence(matcherFn: SequenceGrammar) {
        handleResult(tryMatchSequence(matcherFn, context, input))
    }

    override fun eitherOf(mismatchIsAmbiguous: Boolean, matcherFn: Grammar) {
        handleResult(tryMatchEitherOf(matcherFn, context, input, mismatchIsAmbiguous))
    }

    override fun atLeast(n: Int, matcherFn: SequenceGrammar) {
        handleResult(tryMatchRepeating(SequenceGrammarRule(matcherFn), IntRange(n, Int.MAX_VALUE), context, input))
    }

    override fun identifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>) {
        handleResult(tryMatchIdentifier(input, acceptedOperators, acceptedKeywords))
    }

    override fun optional(rule: Rule<*>) {
        handleResult(tryMatchOptional(rule, context, input))
    }

    override fun optional(matcherFn: SequenceGrammar) {
        handleResult(tryMatchOptional(SequenceGrammarRule(matcherFn), context, input))
    }
}
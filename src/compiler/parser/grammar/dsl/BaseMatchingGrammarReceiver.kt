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
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.reportings.MissingTokenReporting
import compiler.reportings.Reporting
import compiler.reportings.TokenMismatchReporting

internal abstract class BaseMatchingGrammarReceiver(internal val input: TokenSequence) : GrammarReceiver {
    /**
     * Is called by all other methods as soon as there is a matching result
     */
    protected abstract fun handleResult(result: RuleMatchingResult<*>)

    override fun tokenEqualTo(equalTo: Token) {
        if (!input.hasNext()) {
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
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
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.DEFINITIVE,
                token,
                emptySet()
            ))
            return
        }
        else {
            input.rollback()
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                null,
                setOf(
                    TokenMismatchReporting(equalTo, token)
                )
            ))
            return
        }
    }

    override fun tokenOfType(type: TokenType) {
        if (!input.hasNext()) {
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
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
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.DEFINITIVE,
                token,
                emptySet()
            ))
            return
        }
        else {
            input.rollback()
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                null,
                setOf(Reporting.parsingError("Expected $type but found $token", token.sourceLocation))
            ))
            return
        }
    }

    override fun ref(rule: Rule<*>) {
        // this branch is for testing only
        if (input.peek() is NestedRuleMockingToken) {
            handleResult(
                RuleMatchingResult.of<Any, Any, Reporting>(
                    (input.next()!! as NestedRuleMockingToken).replacement
                )
            )
        } else {
            handleResult(rule.tryMatch(input))
        }
    }

    override fun sequence(matcherFn: SequenceGrammar) {
        handleResult(tryMatchSequence(matcherFn, input))
    }

    override fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar) {
        handleResult(tryMatchEitherOf(matcherFn, input, mismatchCertainty))
    }

    override fun atLeast(n: Int, matcherFn: SequenceGrammar) {
        handleResult(tryMatchRepeating(SequenceGrammarRule(matcherFn), IntRange(n, Integer.MAX_VALUE), input))
    }

    override fun identifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>) {
        handleResult(tryMatchIdentifier(input, acceptedOperators, acceptedKeywords))
    }

    override fun optional(rule: Rule<*>) {
        handleResult(tryMatchOptional(rule, input))
    }

    override fun optional(matcherFn: SequenceGrammar) {
        handleResult(tryMatchOptional(SequenceGrammarRule(matcherFn), input))
    }
}
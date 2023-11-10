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
import compiler.parser.EOIRule
import compiler.parser.WhitespaceEaterRule

typealias Grammar = GrammarReceiver.() -> Unit

/**
 * Objects implementing this interface receive invocations that describe properties of the rule. The object
 * can then decide what to do based on those invocations (e.g. match the described rules against a token stream
 * or dynamically build a description text)f
 */
interface GrammarReceiver {
    fun tokenEqualTo(equalTo: Token)
    fun tokenOfType(type: TokenType)
    fun ref(rule: Rule<*>)
    fun sequence(matcherFn: SequenceGrammar)
    fun eitherOf(mismatchIsAmbiguous: Boolean, matcherFn: Grammar)
    fun atLeast(n: Int, matcherFn: SequenceGrammar)
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList())
    fun optional(matcherFn: SequenceGrammar)
    fun optional(rule: Rule<*>)

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    fun operator(operator: Operator) {
        tokenEqualTo(OperatorToken(operator))
    }

    fun eitherOf(matcherFn: Grammar) {
        eitherOf(true, matcherFn)
    }

    fun eitherOf(vararg operators: Operator) {
        eitherOf {
            operators.forEach(this::operator)
        }
    }

    fun endOfInput() {
        ref(EOIRule.INSTANCE)
    }

    fun optionalWhitespace() {
        ref(WhitespaceEaterRule.INSTANCE)
    }
}
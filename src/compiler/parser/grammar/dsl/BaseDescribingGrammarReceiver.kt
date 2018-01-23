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

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.lexer.Token
import compiler.matching.ResultCertainty
import compiler.parser.rule.Rule

abstract class BaseDescribingGrammarReceiver : GrammarReceiver {
    internal abstract fun handleItem(descriptionOfItem: String)

    override fun tokenEqualTo(token: Token) {
        handleItem(token.toStringWithoutLocation())
    }

    override fun ref(rule: Rule<*>) {
        handleItem(rule.descriptionOfAMatchingThing)
    }

    override fun sequence(matcherFn: SequenceGrammar) {
        handleItem(describeSequenceGrammar(matcherFn))
    }

    override fun eitherOf(resultCertainty: ResultCertainty, matcherFn: Grammar) {
        handleItem(describeEitherOfGrammar(matcherFn))
    }

    override fun atLeast(n: Int, matcherFn: SequenceGrammar) {
        handleItem(describeRepeatingGrammar(matcherFn, IntRange(n, Integer.MAX_VALUE)))
    }

    override fun identifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>) {
        handleItem(describeIdentifier(acceptedOperators, acceptedKeywords))
    }

    override fun optional(matcherFn: SequenceGrammar) {
        handleItem("optional " + describeSequenceGrammar(matcherFn))
    }

    override fun optional(rule: Rule<*>) {
        handleItem("optional " + rule.descriptionOfAMatchingThing)
    }
}
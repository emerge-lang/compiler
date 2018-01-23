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

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult

typealias Grammar = GrammarReceiver.() -> Unit
typealias SequenceGrammar = SequenceRuleDefinitionReceiver.() -> Unit

class SequenceGrammarRule(private val grammar: SequenceGrammar): Rule<List<RuleMatchingResult<*>>> {
    override val descriptionOfAMatchingThing by lazy { describeSequenceGrammar(grammar) }
    override fun tryMatch(input: TokenSequence) = tryMatchSequence(grammar, input)
}

fun sequence(matcherFn: SequenceGrammar) = SequenceGrammarRule(matcherFn)

fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar): Rule<*> {
    return object : Rule<Any?> {
        override val descriptionOfAMatchingThing = describeEitherOfGrammar(matcherFn)
        override fun tryMatch(input: TokenSequence) = tryMatchEitherOf(matcherFn, input, mismatchCertainty)
    }
}

fun eitherOf(matcherFn: Grammar) = eitherOf(ResultCertainty.NOT_RECOGNIZED, matcherFn)

fun <T> Rule<T>.describeAs(description: String): Rule<T> {
    val base = this
    return object : Rule<T> {
        override val descriptionOfAMatchingThing = description

        override fun tryMatch(input: TokenSequence): RuleMatchingResult<T> {
            return base.tryMatch(input)
        }
    }
}

fun <ResultBefore,ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)
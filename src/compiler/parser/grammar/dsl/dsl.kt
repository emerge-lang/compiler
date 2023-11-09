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

class SequenceGrammarRule(
    private val givenName: String? = null,
    private val grammar: SequenceGrammar
): Rule<List<RuleMatchingResult<*>>> {
    constructor(grammar: SequenceGrammar) : this(null, grammar)
    override val descriptionOfAMatchingThing by lazy { givenName ?: describeSequenceGrammar(grammar) }
    override fun tryMatch(input: TokenSequence) = tryMatchSequence(grammar, input)
}

class EitherOfGrammarRule(
    private val givenName: String?,
    private val mismatchCertainty: ResultCertainty,
    private val options: Grammar,
) : Rule<Any> {
    override val descriptionOfAMatchingThing by lazy { givenName ?: describeEitherOfGrammar(options) }
    override fun tryMatch(input: TokenSequence) = tryMatchEitherOf(options, input, mismatchCertainty) as RuleMatchingResult<Any>
}

fun sequence(name: String? = null, matcherFn: SequenceGrammar) = SequenceGrammarRule(name, matcherFn)

fun eitherOf(name: String? = null, mismatchCertainty: ResultCertainty = ResultCertainty.NOT_RECOGNIZED, options: Grammar): Rule<*> {
    return EitherOfGrammarRule(name, mismatchCertainty, options)
}

fun <ResultBefore, ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)
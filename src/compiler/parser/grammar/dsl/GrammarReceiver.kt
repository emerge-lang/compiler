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
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.EoiRule
import compiler.parser.grammar.rule.WhitespaceEaterRule
import compiler.parser.grammar.rule.*

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
    fun sequence(grammar: Grammar)
    fun eitherOf(grammar: Grammar)
    fun repeating(grammar: Grammar)
    fun repeatingAtLeastOnce(grammar: Grammar)
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList())
    fun optional(grammar: Grammar)

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    fun operator(operator: Operator) {
        tokenEqualTo(OperatorToken(operator))
    }

    fun eitherOf(vararg operators: Operator) {
        this.eitherOf {
            operators.forEach(this::operator)
        }
    }

    fun endOfInput() {
        ref(EoiRule.INSTANCE)
    }

    fun optionalWhitespace() {
        ref(WhitespaceEaterRule.INSTANCE)
    }
}

class RuleCollectingGrammarReceiver private constructor() : GrammarReceiver {
    private val rules = mutableListOf<Rule<*>>()

    private fun addRule(rule: Rule<*>, asRef: Boolean) {
        rules.add(rule)
    }

    override fun tokenEqualTo(equalTo: Token) {
        addRule(SingleTokenByEqualityRule(equalTo), false)
    }

    override fun tokenOfType(type: TokenType) {
        addRule(SingleTokenByTypeRule(type), false)
    }

    override fun ref(rule: Rule<*>) {
        addRule(rule, true)
    }

    override fun sequence(grammar: Grammar) {
        addRule(collect(grammar, ::SequenceRule), false)
    }

    override fun eitherOf(grammar: Grammar) {
        addRule(collect(grammar, ::EitherOfRule), false)
    }

    override fun repeating(grammar: Grammar) {
        addRule(RepeatingRule(collect(grammar, ::SequenceRule), requireAtLeastOnce = false), false)
    }

    override fun repeatingAtLeastOnce(grammar: Grammar) {
        addRule(RepeatingRule(collect(grammar, ::SequenceRule), requireAtLeastOnce = true), false)
    }

    override fun identifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>) {
        addRule(
            IdentifierRule(acceptedOperators.toSet(), acceptedKeywords.toSet()),
            false,
        )
    }

    override fun optional(grammar: Grammar) {
        addRule(
            RepeatingRule(collect(grammar, ::SequenceRule), requireAtLeastOnce = false, maxRepeats = 1),
            false,
        )
    }

    companion object {
        /**
         * Runs the given [grammar] to discover all its rules. If it produces only a single rule and [optimizeSingleRule],
         * that rule is returned directly. If it produces more than once, the list of rules is passed through
         * [combinedBuilder] so you can get a [SequenceRule] or [EitherOfRule], depending on context.
         */
        fun collect(grammar: Grammar, combinedBuilder: (List<Rule<*>>) -> Rule<*>, optimizeSingleRule: Boolean = true): Rule<*> {
            val collector = RuleCollectingGrammarReceiver()
            collector.grammar()
            if (optimizeSingleRule && collector.rules.size == 1) {
                return collector.rules.single()
            }
            
            return combinedBuilder(collector.rules)
        }
    }
}
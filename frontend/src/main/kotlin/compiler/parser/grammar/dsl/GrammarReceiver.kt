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

import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.parser.grammar.rule.DelimitedIdentifierContentRule
import compiler.parser.grammar.rule.EndOfInputRule
import compiler.parser.grammar.rule.NumericLiteralRule
import compiler.parser.grammar.rule.RepeatingRule
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule
import compiler.parser.grammar.rule.StringLiteralContentRule
import compiler.parser.grammar.rule.TokenEqualToRule

typealias Grammar = GrammarReceiver.() -> Unit

/**
 * Objects implementing this interface receive invocations that describe properties of the rule. The object
 * can then decide what to do based on those invocations (e.g. match the described rules against a token stream
 * or dynamically build a description text)
 */
abstract class GrammarReceiver {
    abstract fun ref(rule: Rule<*>)

    fun tokenEqualTo(equalTo: Token) {
        ref(TokenEqualToRule(equalTo))
    }

    fun sequence(grammar: Grammar) {
        ref(sequence(null, grammar))
    }

    fun eitherOf(grammar: Grammar) {
        ref(eitherOf(null, grammar))
    }

    fun eitherOf(vararg operators: Operator) {
        eitherOf {
            for (op in operators) {
                operator(op)
            }
        }
    }

    fun repeating(grammar: Grammar) {
        ref(RepeatingRule(sequence(null, grammar), false, UInt.MAX_VALUE))
    }

    fun repeatingAtLeastOnce(grammar: Grammar) {
        ref(RepeatingRule(sequence(null, grammar), true, UInt.MAX_VALUE))
    }

    fun delimitedIdentifierContent() {
        ref(DelimitedIdentifierContentRule)
    }

    fun numericLiteral() {
        ref(NumericLiteralRule)
    }

    fun stringLiteralContent() {
        ref(StringLiteralContentRule)
    }

    fun optional(grammar: Grammar) {
        ref(RepeatingRule(sequence(null, grammar), false, 1u))
    }

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    /** TODO: yeet; local keywords are an antipattern, there's a reson modern langs don't have that anymore. Kotlin is an odd one out */
    fun localKeyword(expectedIdentifier: String) {
        tokenEqualTo(IdentifierToken(expectedIdentifier))
    }

    fun operator(operator: Operator) {
        tokenEqualTo(OperatorToken(operator))
    }

    fun endOfInput() {
        ref(EndOfInputRule)
    }
}

class RuleCollectingGrammarReceiver private constructor() : GrammarReceiver() {
    private val rules = mutableListOf<Rule<*>>()

    override fun ref(rule: Rule<*>) {
        rules.add(rule)
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
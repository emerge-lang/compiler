@file:JvmName("GrammarDsl")
package compiler.parser.grammar.dsl

import compiler.parser.grammar.rule.EitherOfRule
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule

fun sequence(givenName: String? = null, grammar: Grammar): Rule<*> {
    return SequenceRule(RuleCollectingGrammarReceiver.collect(grammar), givenName)
}

fun eitherOf(givenName: String? = null, grammar: Grammar): Rule<*> {
    return EitherOfRule(RuleCollectingGrammarReceiver.collect(grammar), givenName)
}
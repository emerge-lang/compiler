@file:JvmName("GrammarDsl")
package compiler.parser.grammar.dsl

import compiler.parser.grammar.rule.EitherOfRule
import compiler.parser.grammar.rule.LazyRule
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule

// TODO: replace with delegate, derive name from declaration?
// val ReturnStatement by sequence { ... }, infers name = "return statement"
fun sequence(explicitName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        RuleCollectingGrammarReceiver.collect(
            grammar,
            { rules -> SequenceRule(rules.toTypedArray(), explicitName) },
            explicitName == null,
        )
    }
}

fun eitherOf(explicitName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        RuleCollectingGrammarReceiver.collect(
            grammar,
            { rules -> EitherOfRule(rules, explicitName) },
            explicitName == null,
        )
    }
}

/**
 * TODO: probably a NOOP, remove if it proves true
 */
val <T : Any> Rule<T>.isolateCyclicGrammar: Rule<T> get() = object : Rule<T> {
    override val explicitName: String? get() = this@isolateCyclicGrammar.explicitName
    override fun startMatching(continueWith: MatchingContinuation<T>) = this@isolateCyclicGrammar.startMatching(continueWith)
}
@file:JvmName("GrammarDsl")
package compiler.parser.grammar.dsl

import compiler.parser.TokenSequence
import compiler.parser.grammar.rule.*

fun sequence(explicitName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        SequenceRule(RuleCollectingGrammarReceiver.collect(grammar), explicitName)
    }
}

fun eitherOf(explicitName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        EitherOfRule(RuleCollectingGrammarReceiver.collect(grammar), explicitName)
    }
}

val <T> Rule<T>.isolateCyclicGrammar: Rule<T> get() = object : Rule<T> {
    override val explicitName: String? get() = this@isolateCyclicGrammar.explicitName
    override val descriptionOfAMatchingThing get() = this@isolateCyclicGrammar.descriptionOfAMatchingThing

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<T> {
        return this@isolateCyclicGrammar.tryMatch(context, input)
    }

    override fun markAmbiguityResolved(inContext: Any) {

    }

    override val minimalMatchingSequence = sequenceOf(emptySequence<ExpectedToken>())
}
@file:JvmName("GrammarDsl")
package compiler.parser.grammar.dsl

import compiler.parser.TokenSequence
import compiler.parser.grammar.rule.*

fun sequence(givenName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        SequenceRule(RuleCollectingGrammarReceiver.collect(grammar), givenName)
    }
}

fun eitherOf(givenName: String? = null, grammar: Grammar): Rule<*> {
    return LazyRule {
        EitherOfRule(RuleCollectingGrammarReceiver.collect(grammar), givenName)
    }
}

val <T> Rule<T>.withEmptyMinimalMatchingSequence: Rule<T> get() = object : Rule<T> {
    override val descriptionOfAMatchingThing get() = this@withEmptyMinimalMatchingSequence.descriptionOfAMatchingThing

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<T> {
        return this@withEmptyMinimalMatchingSequence.tryMatch(context, input)
    }

    override val minimalMatchingSequence = sequenceOf(emptySequence<ExpectedToken>())
}
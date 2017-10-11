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
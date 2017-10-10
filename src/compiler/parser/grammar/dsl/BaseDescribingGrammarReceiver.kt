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
}
package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.lexer.Token
import compiler.matching.ResultCertainty
import compiler.parser.MissingTokenReporting
import compiler.parser.TokenMismatchReporting
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl

internal abstract class BaseMatchingGrammarReceiver(internal val input: TokenSequence) : GrammarReceiver {
    /**
     * Is called by all other methods as soon as there is a matching result
     */
    protected abstract fun handleResult(result: RuleMatchingResult<*>)

    override fun tokenEqualTo(equalTo: Token) {
        if (!input.hasNext()) {
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                null,
                setOf(
                    MissingTokenReporting(equalTo, input.currentSourceLocation)
                )
            ))
            return
        }

        input.mark()

        val token = input.next()!!
        if (token == equalTo) {
            input.commit()
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.DEFINITIVE,
                token,
                emptySet()
            ))
            return
        }
        else {
            input.rollback()
            handleResult(RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                null,
                setOf(
                    TokenMismatchReporting(equalTo, token)
                )
            ))
            return
        }
    }

    override fun ref(rule: Rule<*>) {
        handleResult(rule.tryMatch(input))
    }

    override fun sequence(matcherFn: SequenceGrammar) {
        handleResult(tryMatchSequence(matcherFn, input))
    }

    override fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar) {
        handleResult(tryMatchEitherOf(matcherFn, input, mismatchCertainty))
    }

    override fun atLeast(n: Int, matcherFn: SequenceGrammar) {
        handleResult(tryMatchRepeating(SequenceGrammarRule(matcherFn), IntRange(n, Integer.MAX_VALUE), input))
    }

    override fun identifier(acceptedOperators: Collection<Operator>, acceptedKeywords: Collection<Keyword>) {
        handleResult(tryMatchIdentifier(input, acceptedOperators, acceptedKeywords))
    }
}
package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.Token
import compiler.matching.ResultCertainty
import compiler.parser.rule.EOIRule
import compiler.parser.rule.Rule

/**
 * Objects implementing this interface receive invocations that describe properties of the rule. The object
 * can then decide what to do based on those invocations (e.g. match the described rules against a token stream
 * or dynamically build a description text)f
 */
interface GrammarReceiver {
    fun tokenEqualTo(token: Token)
    fun ref(rule: Rule<*>)
    fun sequence(matcherFn: SequenceGrammar)
    fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar)
    fun atLeast(n: Int, matcherFn: SequenceGrammar)
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList())

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    fun eitherOf(matcherFn: Grammar) {
        eitherOf(ResultCertainty.NOT_RECOGNIZED, matcherFn)
    }

    fun endOfInput() {
        ref(EOIRule.INSTANCE)
    }

    /*fun optional(matcherFn: GrammarReceiver.() -> Any)*/
}
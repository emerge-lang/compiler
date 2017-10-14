package compiler.parser.grammar.dsl

import compiler.lexer.*
import compiler.matching.ResultCertainty
import compiler.parser.rule.EOIRule
import compiler.parser.rule.Rule
import compiler.parser.rule.WhitespaceEaterRule

/**
 * Objects implementing this interface receive invocations that describe properties of the rule. The object
 * can then decide what to do based on those invocations (e.g. match the described rules against a token stream
 * or dynamically build a description text)f
 */
interface GrammarReceiver {
    fun tokenEqualTo(token: Token)
    fun tokenOfType(type: TokenType)
    fun ref(rule: Rule<*>)
    fun sequence(matcherFn: SequenceGrammar)
    fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar)
    fun atLeast(n: Int, matcherFn: SequenceGrammar)
    fun identifier(acceptedOperators: Collection<Operator> = emptyList(), acceptedKeywords: Collection<Keyword> = emptyList())
    fun optional(matcherFn: SequenceGrammar)
    fun optional(rule: Rule<*>)

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    fun operator(operator: Operator) {
        tokenEqualTo(OperatorToken(operator))
    }

    fun eitherOf(matcherFn: Grammar) {
        eitherOf(ResultCertainty.NOT_RECOGNIZED, matcherFn)
    }

    fun eitherOf(vararg operators: Operator) {
        eitherOf {
            operators.forEach(this::operator)
        }
    }

    fun endOfInput() {
        ref(EOIRule.INSTANCE)
    }

    fun optionalWhitespace() {
        ref(WhitespaceEaterRule.INSTANCE)
    }
}
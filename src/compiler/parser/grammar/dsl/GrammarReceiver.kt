package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Token

/**
 * Objects implementing this interface receive invocations that describe properties of the rule. The object
 * can then decide what to do based on those invocations (e.g. match the described rules against a token stream
 * or dynamically build a description text)f
 */
interface GrammarReceiver {
    fun tokenEqualTo(token: Token)

    fun keyword(keyword: Keyword) {
        tokenEqualTo(KeywordToken(keyword))
    }

    // fun sequence(matcherFn: GrammarReceiver.() -> Any)
    /*fun eitherOf(matcherFn: GrammarReceiver.() -> Any)
    fun atLeast(n: Int, itemMatcherFn: GrammarReceiver.() -> Any)
    fun optional(matcherFn: GrammarReceiver.() -> Any)*/
}
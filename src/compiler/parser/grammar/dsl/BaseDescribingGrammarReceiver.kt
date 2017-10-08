package compiler.parser.grammar.dsl

import compiler.lexer.Token

abstract class BaseDescribingGrammarReceiver : GrammarReceiver {
    internal abstract fun handleItem(descriptionOfItem: String)

    override fun tokenEqualTo(token: Token) {
        handleItem(token.toStringWithoutLocation())
    }
}
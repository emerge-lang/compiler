package compiler.parser.grammar.rule

import compiler.lexer.EndOfInputToken

object EndOfInputRule : SingleTokenRule<EndOfInputToken>("end of input", { token -> token as? EndOfInputToken }) {
    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitEndOfInput()
    }
}
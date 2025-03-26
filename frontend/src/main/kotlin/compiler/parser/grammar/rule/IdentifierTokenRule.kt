package compiler.parser.grammar.rule

import compiler.lexer.IdentifierToken

object IdentifierTokenRule : SingleTokenRule<IdentifierToken>("a non-delimited identifier", { token -> token as? IdentifierToken }) {
    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitNonDelimitedIdentifier()
    }
}
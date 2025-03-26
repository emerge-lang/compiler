package compiler.parser.grammar.rule

import compiler.lexer.StringLiteralContentToken

object StringLiteralContentRule : SingleTokenRule<StringLiteralContentToken>("string content", { token -> token as? StringLiteralContentToken }) {
    override fun <R : Any> visit(visitor: GrammarVisitor<R>) {
        visitNoReference(visitor)
    }

    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitStringContent()
    }
}
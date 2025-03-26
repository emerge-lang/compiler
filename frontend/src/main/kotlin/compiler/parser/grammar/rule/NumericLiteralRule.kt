package compiler.parser.grammar.rule

import compiler.lexer.NumericLiteralToken

object NumericLiteralRule : SingleTokenRule<NumericLiteralToken>("numeric literal", { token -> token as? NumericLiteralToken }) {
    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitNumericLiteral()
    }
}
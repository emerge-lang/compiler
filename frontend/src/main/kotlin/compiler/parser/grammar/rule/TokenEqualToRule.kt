package compiler.parser.grammar.rule

import compiler.lexer.Token

class TokenEqualToRule(val expectedToken: Token) : SingleTokenRule<Token>(
    expectedToken.toStringWithoutLocation(),
    { token -> token.takeIf { it  == expectedToken }}
) {
    override fun <R : Any> visit(visitor: GrammarVisitor<R>) {
        visitNoReference(visitor)
    }

    override fun <R : Any> visitNoReference(visitor: GrammarVisitor<R>) {
        visitor.visitExpectedIdenticalToken(expectedToken)
    }
}
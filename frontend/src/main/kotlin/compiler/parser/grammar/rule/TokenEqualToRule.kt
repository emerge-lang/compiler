package compiler.parser.grammar.rule

import compiler.lexer.Token

class TokenEqualToRule(val expectedToken: Token) : SingleTokenRule<Token>(
    expectedToken.toStringWithoutLocation(),
    { token -> token.takeIf { it  == expectedToken }}
)
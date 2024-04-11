package compiler.parser.grammar.dsl

import compiler.lexer.Token
import compiler.parser.grammar.rule.SingleTokenRule

class TokenEqualToRule(val expectedToken: Token) : SingleTokenRule<Token>(expectedToken.toStringWithoutLocation(), { token -> token.takeIf { it  == expectedToken }})
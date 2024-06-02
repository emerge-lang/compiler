package compiler.parser.grammar.rule

import compiler.lexer.IdentifierToken

object IdentifierTokenRule : SingleTokenRule<IdentifierToken>("a non-delimited identifier", { token -> token as? IdentifierToken })
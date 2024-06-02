package compiler.parser.grammar.rule

import compiler.lexer.StringLiteralContentToken

object StringLiteralContentRule : SingleTokenRule<StringLiteralContentToken>("string content", { token -> token as? StringLiteralContentToken })
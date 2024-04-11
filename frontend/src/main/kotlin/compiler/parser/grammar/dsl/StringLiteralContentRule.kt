package compiler.parser.grammar.dsl

import compiler.lexer.StringLiteralContentToken
import compiler.parser.grammar.rule.SingleTokenRule

object StringLiteralContentRule : SingleTokenRule<StringLiteralContentToken>("string content", { token -> token as? StringLiteralContentToken })
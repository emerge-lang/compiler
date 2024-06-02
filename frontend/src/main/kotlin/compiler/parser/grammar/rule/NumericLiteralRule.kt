package compiler.parser.grammar.rule

import compiler.lexer.NumericLiteralToken

object NumericLiteralRule : SingleTokenRule<NumericLiteralToken>("numeric literal", { token -> token as? NumericLiteralToken })
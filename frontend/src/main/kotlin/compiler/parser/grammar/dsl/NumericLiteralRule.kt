package compiler.parser.grammar.dsl

import compiler.lexer.NumericLiteralToken
import compiler.parser.grammar.rule.SingleTokenRule

object NumericLiteralRule : SingleTokenRule<NumericLiteralToken>("numeric literal", { token -> token as? NumericLiteralToken })
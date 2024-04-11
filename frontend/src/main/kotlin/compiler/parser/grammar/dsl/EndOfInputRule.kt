package compiler.parser.grammar.dsl

import compiler.lexer.EndOfInputToken
import compiler.parser.grammar.rule.SingleTokenRule

object EndOfInputRule : SingleTokenRule<EndOfInputToken>("end of input", { token -> token as? EndOfInputToken })
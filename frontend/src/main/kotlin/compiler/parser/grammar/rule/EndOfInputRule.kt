package compiler.parser.grammar.rule

import compiler.lexer.EndOfInputToken

object EndOfInputRule : SingleTokenRule<EndOfInputToken>("end of input", { token -> token as? EndOfInputToken })
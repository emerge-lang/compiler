package compiler.parser.grammar.rule

import compiler.lexer.DelimitedIdentifierContentToken

object DelimitedIdentifierContentRule : SingleTokenRule<DelimitedIdentifierContentToken>("delimited identifier content", { token -> token as? DelimitedIdentifierContentToken })
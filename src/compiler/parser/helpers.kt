package compiler.parser

import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.Token

fun isWhitespace(token: Token): Boolean = token == OperatorToken(Operator.NEWLINE)
fun isWhitespace(thing: Any): Boolean = thing is Token && isWhitespace(thing as Token)

package compiler.ast

import compiler.ast.expression.Expression
import compiler.lexer.KeywordToken

class ReturnStatement(
    val returnKeyword: KeywordToken,
    val expression: Expression
) : Executable
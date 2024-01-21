package compiler.ast

import compiler.lexer.IdentifierToken

class ASTPackageName(
    val names: List<IdentifierToken>,
)
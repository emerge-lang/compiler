package compiler.ast

import compiler.lexer.IdentifierToken

class VariableDeclaration(
    val name: IdentifierToken,
    val type: TypeReference?,
    val assignable: Boolean,
    val assignExpression: Any? // Expression
)
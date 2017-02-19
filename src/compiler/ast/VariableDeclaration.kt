package compiler.ast

import compiler.ast.types.TypeModifier
import compiler.lexer.IdentifierToken

class VariableDeclaration(
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val assignable: Boolean,
    val assignExpression: Any? // Expression
)
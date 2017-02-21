package compiler.ast

import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken

class VariableDeclaration(
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val assignable: Boolean,
    val assignExpression: Any? // Expression
)
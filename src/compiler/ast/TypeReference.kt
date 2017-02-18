package compiler.ast

import compiler.lexer.IdentifierToken

class TypeReference(
    val typeName: IdentifierToken,
    val isNullable: Boolean
)
package compiler.ast

import compiler.ast.types.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken

class FunctionDeclaration(
    val declaredWith: KeywordToken,
    val name: IdentifierToken,
    val parameters: ParameterList,
    val returnType: TypeReference
)
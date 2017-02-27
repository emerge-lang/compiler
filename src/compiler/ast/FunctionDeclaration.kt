package compiler.ast

import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val name: IdentifierToken,
    val parameters: ParameterList,
    val returnType: TypeReference
) : Declaration
{
    val signature = FunctionSignature(parameters.types, returnType)
}
package compiler.ast

import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken

class ParameterList (
    val parameters: List<Parameter> = emptyList()
) {
    /** The types; null values indicate non-specified parameters */
    val types: List<TypeReference?> = parameters.map { it.type }
}

class Parameter (
    val name: IdentifierToken,
    val type: TypeReference?
)
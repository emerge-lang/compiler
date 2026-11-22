package compiler.parser

import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.lexer.OperatorToken

data class AstIntersectionTypePostfix(
    val intersectionOperator: OperatorToken,
    val reference: NamedTypeReference,
)

data class AstUnionTypePostfix(
    val unionOperator: OperatorToken,
    /** a named type or an intersection */
    val reference: TypeReference,
)
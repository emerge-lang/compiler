package compiler.parser

import compiler.ast.type.NamedTypeReference
import compiler.lexer.OperatorToken

data class AstIntersectionTypePostfix(
    val intersectionOperator: OperatorToken,
    val reference: NamedTypeReference,
)
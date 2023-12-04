package compiler.ast.type

data class TypeParameter(
    val reference: TypeReference,
    val bound: TypeReference?,
)
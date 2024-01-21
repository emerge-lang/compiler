package compiler.ast.type

import compiler.lexer.SourceLocation

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
data class TypeArgument(
    val variance: TypeVariance,
    val type: TypeReference,
) {
    val sourceLocation: SourceLocation? = type.sourceLocation

    override fun toString(): String {
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        return str + type.toString()
    }
}
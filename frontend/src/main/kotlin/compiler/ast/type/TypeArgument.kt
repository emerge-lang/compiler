package compiler.ast.type

import compiler.lexer.Span

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
data class TypeArgument(
    val variance: TypeVariance,
    val type: TypeReference,
) {
    val span: Span? = type.span

    override fun toString(): String {
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        return str + type.toString()
    }
}
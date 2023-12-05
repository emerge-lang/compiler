package compiler.ast.type

import compiler.lexer.IdentifierToken

/**
 * Type parameterization on the declaring side.
 * @see TypeArgument
 */
data class TypeParameter(
    val variance: TypeVariance,
    val name: IdentifierToken,
    val bound: TypeReference?,
) {
    override fun toString(): String {
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        str += name

        if (bound != null) {
            str += " : "
            str += bound.toString()
        }

        return str
    }
}
package compiler.ast.type

import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
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
    fun bindTo(context: CTContext): BoundTypeParameter {
        return BoundTypeParameter(this, context)
    }

    override fun toString(): String {
        var str = ""
        if (variance != TypeVariance.UNSPECIFIED) {
            str += variance.name.lowercase()
            str += " "
        }

        str += name.value

        if (bound != null) {
            str += " : "
            str += bound.toString()
        }

        return str
    }
}
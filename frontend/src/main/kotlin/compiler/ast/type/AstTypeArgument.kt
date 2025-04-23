package compiler.ast.type

import compiler.lexer.Span
import compiler.lexer.Token

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
sealed interface AstTypeArgument {
    val span: Span?

    data class Reference(
        val variance: TypeVariance,
        val type: TypeReference,
    ) : AstTypeArgument {
        override val span: Span? = type.span

        override fun toString(): String {
            var str = ""
            if (variance != TypeVariance.UNSPECIFIED) {
                str += variance.name.lowercase()
                str += " "
            }

            return str + type.toString()
        }
    }

    class Wildcard(val token: Token) : AstTypeArgument {
        override val span = token.span
    }
}
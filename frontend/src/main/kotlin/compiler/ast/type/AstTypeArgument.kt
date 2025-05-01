package compiler.ast.type

import compiler.lexer.Span
import compiler.lexer.Token

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
sealed interface AstTypeArgument {
    val span: Span?
    val astVariance: AstTypeVariance?
    val variance: TypeVariance get()= astVariance?.value ?: TypeVariance.UNSPECIFIED

    data class Reference(
        override val astVariance: AstTypeVariance?,
        val type: TypeReference,
    ) : AstTypeArgument {
        override val span: Span? = type.span

        override fun toString(): String {
            var str = ""
            if (astVariance != null) {
                str += astVariance.token.keyword.text
                str += " "
            }

            return str + type.toString()
        }
    }

    data class Wildcard(
        override val astVariance: AstTypeVariance?,
        val token: Token
    ) : AstTypeArgument {
        override val span = token.span

        override fun toString(): String {
            var str = ""
            if (astVariance != null) {
                str += astVariance.token.keyword.text
                str += " "
            }
            return "$str*"
        }
    }
}
package compiler.ast.type

import compiler.lexer.Operator
import compiler.lexer.Span

sealed interface AstTypeArgument {
    val variance: TypeVariance
    val span: Span?
}

/**
 * Type parameterization on the referencing side.
 * @see TypeParameter
 */
data class AstSpecificTypeArgument(
    override val variance: TypeVariance,
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

class AstWildcardTypeArgument private constructor(
    override val variance: TypeVariance,
    override val span: Span? = null,
) : AstTypeArgument {
    override fun toString(): String = Operator.TIMES.text

    companion object {
        val INSTANCE = AstWildcardTypeArgument(TypeVariance.UNSPECIFIED)

        operator fun invoke(variance: TypeVariance, span: Span) = AstWildcardTypeArgument(variance, span)
    }
}
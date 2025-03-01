package compiler.reportings

import compiler.ast.type.TypeParameter
import compiler.binding.type.BoundTypeArgument
import compiler.lexer.Span

class TypeArgumentVarianceMismatchDiagnostic(
    val parameter: TypeParameter,
    val argument: BoundTypeArgument,
) : Diagnostic(
    Level.ERROR,
    "The variance in the type argument conflicts with the variance on the declaration of ${parameter.name.span} (declared as ${parameter.variance.name.lowercase()})",
    argument.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeArgumentVarianceMismatchDiagnostic

        if (argument != other.argument) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = argument.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}
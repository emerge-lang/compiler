package compiler.reportings

import compiler.binding.type.BoundTypeArgument
import compiler.lexer.Span

class TypeArgumentVarianceSuperfluousDiagnostic(
    val argument: BoundTypeArgument,
) : Diagnostic(
    Level.WARNING,
    "Superfluous variance on type argument. The parameter is already declared as ${argument.variance.name.lowercase()}",
    argument.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeArgumentVarianceSuperfluousDiagnostic

        return argument == other.argument && argument.span == other.argument.span
    }

    override fun hashCode(): Int {
        var result = argument.hashCode()
        result = result * 31 + argument.span.hashCode()
        return result
    }
}
package compiler.reportings

import compiler.ast.type.TypeParameter
import compiler.binding.type.BoundTypeArgument
import compiler.lexer.Span

class TypeArgumentOutOfBoundsDiagnostic(
    val parameter: TypeParameter,
    val argument: BoundTypeArgument,
    val reason: String,
) : Diagnostic(
    Level.ERROR,
    "Argument for type parameter ${parameter.name.value} is not within the bound: $reason",
    argument.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeArgumentOutOfBoundsDiagnostic

        if (parameter != other.parameter) return false
        if (argument != other.argument) return false
        if (argument.span != other.argument.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = parameter.hashCode()
        result = 31 * result + argument.hashCode()
        result = 31 * result + argument.span.hashCode()
        return result
    }
}
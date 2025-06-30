package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.binding.type.BoundTypeArgument
import compiler.lexer.Span

class TypeArgumentOutOfBoundsDiagnostic(
    val parameter: TypeParameter,
    val argument: BoundTypeArgument,
    val reason: String,
) : Diagnostic(
    Severity.ERROR,
    "Argument for type parameter ${parameter.name.value} is not within the bound: $reason",
    argument.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeArgumentOutOfBoundsDiagnostic

        return this.span == other.span
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}
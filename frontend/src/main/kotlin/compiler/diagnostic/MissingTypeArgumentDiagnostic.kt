package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.lexer.Span

class MissingTypeArgumentDiagnostic(
    val parameter: TypeParameter,
    span: Span,
) : Diagnostic(
    Level.ERROR,
    "No argument supplied for type parameter ${parameter.name.value}",
    span,
) {
    override fun toString() = super.toString()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MissingTypeArgumentDiagnostic) return false

        if (parameter != other.parameter) return false
        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = parameter.hashCode()
        result = result * 31 + span.hashCode()
        return result
    }
}
package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.lexer.Span

class TypeParameterBoundedByItselfDiagnostic(
    val parameter: TypeParameter,
    referenceSpan: Span,
) : Diagnostic(
    Severity.ERROR,
    "Type parameter ${parameter.name.value} cannot bound itself; it can only appear in the type arguments of its bound, as in ${parameter.name.value} : Comparable<${parameter.name.value}>",
    referenceSpan,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeParameterBoundedByItselfDiagnostic) return false

        return this.span == other.span
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}

package compiler.diagnostic

import compiler.ast.type.TypeReference
import compiler.lexer.Span

data class ExplicitInferTypeNotAllowedDiagnostic(
    val reference: TypeReference,
) : Diagnostic(
    Severity.ERROR,
    "Inferring the type is not allowed or possible here",
    reference.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
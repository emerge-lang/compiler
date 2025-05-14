package compiler.diagnostic

import compiler.ast.type.NamedTypeReference
import compiler.lexer.Span

data class ExplicitInferTypeWithArgumentsDiagnostic(
    val reference: NamedTypeReference,
) : Diagnostic(
    Severity.ERROR,
    "Type arguments cannot be specified for types that should be inferred.",
    reference.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
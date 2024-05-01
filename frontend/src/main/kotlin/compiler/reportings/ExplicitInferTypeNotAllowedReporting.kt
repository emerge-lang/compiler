package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.Span

data class ExplicitInferTypeNotAllowedReporting(
    val reference: TypeReference,
) : Reporting(
    Level.ERROR,
    "Inferring the type is not allowed or possible here",
    reference.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
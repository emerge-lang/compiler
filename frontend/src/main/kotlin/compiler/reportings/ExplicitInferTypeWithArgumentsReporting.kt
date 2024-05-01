package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.Span

data class ExplicitInferTypeWithArgumentsReporting(
    val reference: TypeReference,
) : Reporting(
    Level.ERROR,
    "Type arguments cannot be specified for types that should be inferred.",
    reference.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
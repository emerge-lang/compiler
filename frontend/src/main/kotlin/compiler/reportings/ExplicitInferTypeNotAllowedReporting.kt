package compiler.reportings

import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation

data class ExplicitInferTypeNotAllowedReporting(
    val reference: TypeReference,
) : Reporting(
    Level.ERROR,
    "Inferring the type is not allowed or possible here",
    reference.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun toString() = super.toString()
}
package compiler.diagnostic

import compiler.ast.type.AstTypeArgument
import compiler.lexer.Span

data class SuperfluousTypeArgumentsDiagnostic(
    val nExpected: Int,
    val firstSuperfluousArgument: AstTypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Too many type arguments, expected only $nExpected",
    firstSuperfluousArgument.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
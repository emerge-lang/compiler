package compiler.diagnostic

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

data class SuperfluousTypeArgumentsDiagnostic(
    val nExpected: Int,
    val firstSuperfluousArgument: TypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Too many type arguments, expected only $nExpected",
    firstSuperfluousArgument.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
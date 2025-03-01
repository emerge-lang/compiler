package compiler.reportings

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

data class SuperfluousTypeArgumentsDiagnostic(
    val nExpected: Int,
    val firstSuperfluousArgument: TypeArgument,
) : Diagnostic(
    Level.ERROR,
    "Too many type arguments, expected only $nExpected",
    firstSuperfluousArgument.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
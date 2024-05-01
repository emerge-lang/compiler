package compiler.reportings

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

data class SuperfluousTypeArgumentsReporting(
    val nExpected: Int,
    val firstSuperfluousArgument: TypeArgument,
) : Reporting(
    Level.ERROR,
    "Too many type arguments, expected only $nExpected",
    firstSuperfluousArgument.span ?: Span.UNKNOWN,
) {
    override fun toString() = super.toString()
}
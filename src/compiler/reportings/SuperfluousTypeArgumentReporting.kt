package compiler.reportings

import compiler.ast.type.TypeArgument
import compiler.lexer.SourceLocation

data class SuperfluousTypeArgumentsReporting(
    val nExpected: Int,
    val firstSuperfluousArgument: TypeArgument,
) : Reporting(
    Level.ERROR,
    "Too many type arguments, expected only $nExpected",
    firstSuperfluousArgument.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun toString() = super.toString()
}
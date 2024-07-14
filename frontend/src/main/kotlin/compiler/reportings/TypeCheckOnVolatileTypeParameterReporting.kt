package compiler.reportings

import compiler.lexer.Span

class TypeCheckOnVolatileTypeParameterReporting(
    val typeLocation: Span,
) : Reporting(
    Level.ERROR,
    "Instance-of checks on generic types are not supported yet.",
    typeLocation,
)
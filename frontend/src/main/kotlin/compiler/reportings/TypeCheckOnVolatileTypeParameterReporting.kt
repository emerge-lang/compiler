package compiler.reportings

import compiler.lexer.Span

class TypeCheckOnVolatileTypeParameterReporting(
    val typeLocation: Span,
) : Reporting(
    Level.ERROR,
    "Instance-of checks are only supported on named types.",
    typeLocation,
)
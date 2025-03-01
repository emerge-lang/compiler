package compiler.diagnostic

import compiler.lexer.Span

class TypeCheckOnVolatileTypeParameterDiagnostic(
    val typeLocation: Span,
) : Diagnostic(
    Level.ERROR,
    "Instance-of checks are only supported on named types.",
    typeLocation,
)
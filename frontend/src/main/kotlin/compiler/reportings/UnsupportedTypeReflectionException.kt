package compiler.reportings

import compiler.lexer.Span

class UnsupportedTypeReflectionException(
    val typeLocation: Span,
) : Diagnostic(
    Level.ERROR,
    "Currently, reflection is only supported on named base types",
    typeLocation,
)
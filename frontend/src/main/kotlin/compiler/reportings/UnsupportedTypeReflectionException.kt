package compiler.reportings

import compiler.lexer.Span

class UnsupportedTypeReflectionException(
    val typeLocation: Span,
) : Reporting(
    Level.ERROR,
    "Currently, reflection is only supported on named base types",
    typeLocation,
)
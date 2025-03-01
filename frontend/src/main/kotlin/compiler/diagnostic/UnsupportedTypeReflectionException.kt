package compiler.diagnostic

import compiler.lexer.Span

class UnsupportedTypeReflectionException(
    val typeLocation: Span,
) : Diagnostic(
    Severity.ERROR,
    "Currently, reflection is only supported on named base types",
    typeLocation,
)
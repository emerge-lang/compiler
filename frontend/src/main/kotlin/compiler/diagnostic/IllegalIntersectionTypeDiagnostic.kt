package compiler.diagnostic

import compiler.lexer.Span

class IllegalIntersectionTypeDiagnostic(
    reason: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "This is not a valid intersection type: $reason",
    span,
)
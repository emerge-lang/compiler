package compiler.diagnostic

import compiler.lexer.Span

class InvalidBaseTypeMemberVariableAttributeDiagnostic(
    reason: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "This is not a valid attribute for member variables: $reason",
    span,
)
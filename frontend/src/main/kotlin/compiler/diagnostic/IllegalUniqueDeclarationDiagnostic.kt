package compiler.diagnostic

import compiler.lexer.Span

class IllegalUniqueDeclarationDiagnostic(
    message: String,
    span: Span,
) : Diagnostic(Severity.ERROR, message, span)

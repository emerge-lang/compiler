package compiler.diagnostic

import compiler.lexer.Span

/**
 * Tokens are never `const`: reported for a `const` reference to a token type, and for a token type that is
 * declared `const`.
 */
class ConstTokenDiagnostic(
    val tokenTypeName: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "$tokenTypeName is a token type; tokens cannot be const because they represent mutable external or global state",
    span,
)

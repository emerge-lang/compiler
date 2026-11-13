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
    "$tokenTypeName is a token type; tokens cannot be const",
    span,
)

/**
 * A token type cannot inherit from `NonToken`.
 */
class TokenInheritsNonTokenDiagnostic(
    val tokenTypeName: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "$tokenTypeName is a token type; it cannot inherit from NonToken",
    span,
)

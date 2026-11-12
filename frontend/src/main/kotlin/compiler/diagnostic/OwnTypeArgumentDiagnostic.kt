package compiler.diagnostic

import compiler.lexer.Span

/**
 * `own` is a promise about a single reference; generic code copies values of a type parameter freely.
 */
class OwnTypeArgumentDiagnostic(
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Type arguments cannot be of the mutability own: it would allow generic code to duplicate the reference, which is not allowed for own values. Use mut, const or read here.",
    span,
)

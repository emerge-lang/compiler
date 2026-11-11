package compiler.diagnostic

import compiler.lexer.Span

/**
 * `own` is a promise about a single reference; generic code copies values of a type parameter freely.
 */
class OwnTypeArgumentDiagnostic(
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Type arguments cannot be of the mutability own: generic code may create any number of references to a value of a type parameter. Use mut, const or read here.",
    span,
)

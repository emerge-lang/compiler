package compiler.diagnostic

import compiler.lexer.Span

/**
 * `exclusive` is a promise about a single reference; generic code copies values of a type parameter freely.
 */
class ExclusiveTypeArgumentDiagnostic(
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Type arguments cannot be exclusive: generic code may create any number of references to a value of a type parameter. Use mut, const or read here.",
    span,
)

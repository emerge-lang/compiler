package compiler.diagnostic

import compiler.ast.Expression

class NullCheckingNonNullableValueDiagnostic(
    val nonNullableValue: Expression,
) : Diagnostic(
    Severity.WARNING,
    "this value can never be null, the null-check is superfluous",
    nonNullableValue.span,
)
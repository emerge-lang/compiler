package compiler.reportings

import compiler.ast.Expression

class NullCheckingNonNullableValueDiagnostic(
    val nonNullableValue: Expression,
) : Diagnostic(
    Level.WARNING,
    "this value can never be null, the null-check is superfluous",
    nonNullableValue.span,
)
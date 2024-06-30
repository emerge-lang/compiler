package compiler.reportings

import compiler.ast.Expression

class NullCheckingNonNullableValueReporting(
    val nonNullableValue: Expression,
) : Reporting(
    Level.WARNING,
    "this value can never be null, the null-check is superfluous",
    nonNullableValue.span,
)
package compiler.diagnostic

class MutationInConditionDiagnostic(
    val impurity: PurityViolationDiagnostic.Impurity,
) : Diagnostic(
    Severity.WARNING,
    "This operation is mutating state in a condition.",
    impurity.span,
)
package compiler.diagnostic

import compiler.binding.impurity.Impurity

class MutationInConditionDiagnostic(
    val impurity: Impurity,
) : Diagnostic(
    Severity.WARNING,
    "This operation is mutating state in a condition.",
    impurity.span,
)
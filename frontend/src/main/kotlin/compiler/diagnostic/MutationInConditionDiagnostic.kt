package compiler.diagnostic

import compiler.ast.Executable

class MutationInConditionDiagnostic(
    val mutation: Executable,
) : Diagnostic(
    Severity.WARNING,
    "This operation is mutating state in a condition.",
    mutation.span,
)
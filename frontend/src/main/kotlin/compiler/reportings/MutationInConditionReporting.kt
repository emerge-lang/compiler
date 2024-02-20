package compiler.reportings

import compiler.ast.Executable

class MutationInConditionReporting(
    val mutation: Executable,
) : Reporting(
    Level.WARNING,
    "This operation is mutating state in a condition.",
    mutation.sourceLocation,
)
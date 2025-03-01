package compiler.diagnostic

import compiler.ast.AssignmentStatement

class AssignmenUsedAsExpressionDiagnostic(
    val assignment: AssignmentStatement,
) : Diagnostic(
    Severity.ERROR,
    "Assignments are not expressions.",
    assignment.assignmentOperatorToken.span,
)
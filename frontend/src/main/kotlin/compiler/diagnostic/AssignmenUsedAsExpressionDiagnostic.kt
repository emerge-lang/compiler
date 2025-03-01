package compiler.diagnostic

import compiler.ast.AssignmentStatement

class AssignmenUsedAsExpressionDiagnostic(
    val assignment: AssignmentStatement,
) : Diagnostic(
    Level.ERROR,
    "Assignments are not expressions.",
    assignment.assignmentOperatorToken.span,
)
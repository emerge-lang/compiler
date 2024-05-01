package compiler.reportings

import compiler.ast.AssignmentStatement

class AssignmenUsedAsExpressionReporting(
    val assignment: AssignmentStatement,
) : Reporting(
    Level.ERROR,
    "Assignments are not expressions.",
    assignment.assignmentOperatorToken.span,
)
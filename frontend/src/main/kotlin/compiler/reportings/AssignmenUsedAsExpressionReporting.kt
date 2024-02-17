package compiler.reportings

import compiler.ast.expression.AssignmentExpression

class AssignmenUsedAsExpressionReporting(
    val assignment: AssignmentExpression,
) : Reporting(
    Level.ERROR,
    "Assignments are not expressions. Did you mean to use == ?",
    assignment.assignmentOperatorToken.sourceLocation,
)
package compiler.reportings

import compiler.ast.expression.AssignmentExpression

class AssignmentInConditionReporting(
    val assignment: AssignmentExpression,
) : Reporting(
    Level.ERROR,
    "Conditions cannot contain assignments. Did you mean to use == ?",
    assignment.assignmentOperatorToken.sourceLocation,
)
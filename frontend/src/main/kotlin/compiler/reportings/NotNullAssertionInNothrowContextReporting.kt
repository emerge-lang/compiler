package compiler.reportings

import compiler.ast.expression.NotNullExpression

class NotNullAssertionInNothrowContextReporting(
    val assertion: NotNullExpression,
    val boundary: SideEffectBoundary,
) : Reporting(
    Level.ERROR,
    "Cannot use !! in in nothrow $boundary; it can throw a NullPointerError",
    assertion.notNullOperator.span,
)
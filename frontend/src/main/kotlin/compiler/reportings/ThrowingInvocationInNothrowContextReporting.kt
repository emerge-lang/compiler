package compiler.reportings

import compiler.binding.expression.BoundInvocationExpression

class ThrowingInvocationInNothrowContextReporting(
    val invocation: BoundInvocationExpression,
    val boundary: SideEffectBoundary,
) : Reporting(
    Level.ERROR,
    "Cannot invoke possibly-throwing function ${invocation.functionToInvoke!!.canonicalName} in nothrow $boundary",
    invocation.declaration.span,
)
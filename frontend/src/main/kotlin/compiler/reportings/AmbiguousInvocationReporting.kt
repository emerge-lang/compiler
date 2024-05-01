package compiler.reportings

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundFunction

class AmbiguousInvocationReporting(
    val invocation: InvocationExpression,
    val candidates: List<BoundFunction>,
) : Reporting(
    Reporting.Level.ERROR,
    "Multiple overloads of ${candidates.first().name} apply to this invocation. Disambiguate by casting parameters explicitly.",
    invocation.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as AmbiguousInvocationReporting

        if (invocation != other.invocation) return false

        return true
    }

    override fun hashCode(): Int {
        return invocation.hashCode()
    }
}
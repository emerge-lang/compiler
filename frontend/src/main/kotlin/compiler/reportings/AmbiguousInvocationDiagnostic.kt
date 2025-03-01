package compiler.reportings

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundFunction

class AmbiguousInvocationDiagnostic(
    val invocation: InvocationExpression,
    val candidates: List<BoundFunction>,
) : Diagnostic(
    Diagnostic.Level.ERROR,
    "Multiple overloads of ${candidates.first().name} apply to this invocation. Disambiguate by casting parameters explicitly.",
    invocation.span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(
        SourceHint(invocation.span, "this invocation is ambiguous", true),
        *candidates.map { SourceHint(it.declaredAt, "this is a viable candidate", nLinesContext = 0u) }.toTypedArray(),
    )}"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as AmbiguousInvocationDiagnostic

        if (invocation != other.invocation) return false

        return true
    }

    override fun hashCode(): Int {
        return invocation.hashCode()
    }
}
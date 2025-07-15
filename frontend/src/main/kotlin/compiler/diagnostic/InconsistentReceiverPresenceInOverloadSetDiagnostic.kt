package compiler.diagnostic

import compiler.binding.BoundOverloadSet
import compiler.diagnostic.rendering.CellBuilder

class InconsistentReceiverPresenceInOverloadSetDiagnostic(
    val overloadSet: BoundOverloadSet<*>,
) : Diagnostic(
    Severity.ERROR,
    "Receiver presence is inconsistent in ${overloadSet.canonicalName}. All functions in an overload-set must either declare a receiver or not declare one.",
    overloadSet.overloads.first().declaredAt,
) {
    context(CellBuilder) override fun renderBody() {
        sourceHints(overloadSet.overloads.map {
            SourceHint(it.parameters.declaredReceiver?.declaration?.span ?: it.declaredAt, null, nLinesContext = 0u, severity = severity)
        })
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is InconsistentReceiverPresenceInOverloadSetDiagnostic) return false

        if (overloadSet.canonicalName != other.overloadSet.canonicalName) return false
        if (overloadSet.parameterCount != other.overloadSet.parameterCount) return false

        return true
    }

    override fun hashCode(): Int {
        var result = overloadSet.canonicalName.hashCode()
        result = 31 * result + overloadSet.parameterCount
        return result
    }
}
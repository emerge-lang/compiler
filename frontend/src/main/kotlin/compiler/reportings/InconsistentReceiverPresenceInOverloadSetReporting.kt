package compiler.reportings

import compiler.binding.BoundOverloadSet

class InconsistentReceiverPresenceInOverloadSetReporting(
    val overloadSet: BoundOverloadSet<*>,
) : Reporting(
    Level.ERROR,
    "Receiver presence is inconsistent in ${overloadSet.canonicalName}. All functions in an overload-set must either declare a receiver or not declare one.",
    overloadSet.overloads.first().declaredAt,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(overloadSet.overloads.map {
            SourceHint(it.parameters.declaredReceiver?.declaration?.span ?: it.declaredAt, null, nLinesContext = 0u)
        })

        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is InconsistentReceiverPresenceInOverloadSetReporting) return false

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
package compiler.diagnostic

import compiler.binding.BoundOverloadSet
import compiler.diagnostic.rendering.CellBuilder

class OverloadSetHasNoDisjointParameterDiagnostic(
    val overloadSet: BoundOverloadSet<*>,
) : Diagnostic(
    Severity.ERROR,
    "This overload-set is ambiguous. The types of least one parameter must be disjoint, this set has none.",
    overloadSet.overloads.first().declaredAt,
) {
    val overloadSetName = overloadSet.overloads.first().canonicalName
    val overloadSetParameterCount = overloadSet.overloads.first().parameters.parameters.size

    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(overloadSet.overloads.map { SourceHint(it.declaredAt, severity = severity) })
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is OverloadSetHasNoDisjointParameterDiagnostic) return false

        if (overloadSetName != other.overloadSetName) return false
        if (overloadSetParameterCount != other.overloadSetParameterCount) return false

        return true
    }

    override fun hashCode(): Int {
        var result = overloadSetName.hashCode()
        result = 31 * result + overloadSetParameterCount
        return result
    }
}
package compiler.reportings

import compiler.binding.BoundFunction

class OverloadSetHasNoDisjointParameterReporting(
    val overloads: Iterable<BoundFunction>,
) : Reporting(
    Level.ERROR,
    "This overload-set is ambiguous. The types of least one parameter must be disjoint, this set has none.",
    overloads.first().declaredAt,
) {
    val overloadSetName = overloads.first().fullyQualifiedName
    val overloadSetParameterCount = overloads.first().parameters.parameters.size

    override fun toString(): String {
        var str = levelAndMessage
        overloads
            .groupBy { it.declaredAt.file }
            .forEach { (file, overloadsInFile) ->
                str += "\nin $file:\n"
                str += getIllustrationForHighlightedLines(overloadsInFile.map { it.declaredAt }, 0u)
            }

        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is OverloadSetHasNoDisjointParameterReporting) return false

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
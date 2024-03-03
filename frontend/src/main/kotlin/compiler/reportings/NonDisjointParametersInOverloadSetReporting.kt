package compiler.reportings

import compiler.ast.VariableDeclaration
import io.github.tmarsteel.emerge.backend.api.DotName

class NonDisjointParametersInOverloadSetReporting(
    val overloadSetName: DotName,
    val overloadSetParamaeterCount: Int,
    val disjointIndex: Int,
    val disjointParameters: Collection<VariableDeclaration>,
) : Reporting(
    Level.ERROR,
    "All parameters at anz given index in an overload set must have disjoint types. The types of these parameters are not disjoint.",
    disjointParameters.first().sourceLocation,
) {
    override fun toString(): String {
        var str = levelAndMessage
        disjointParameters
            .groupBy { it.sourceLocation.file }
            .forEach { (file, parametersInFile) ->
                str += "\n\nin${parametersInFile.first().sourceLocation.file}:\n"
                str += getIllustrationForHighlightedLines(parametersInFile.map { it.sourceLocation }, 0u)
            }

        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is NonDisjointParametersInOverloadSetReporting) return false

        if (overloadSetName != other.overloadSetName) return false
        if (overloadSetParamaeterCount != other.overloadSetParamaeterCount) return false
        if (disjointIndex != other.disjointIndex) return false

        return true
    }

    override fun hashCode(): Int {
        var result = overloadSetName.hashCode()
        result = 31 * result + overloadSetParamaeterCount
        result = 31 * result + disjointIndex
        return result
    }
}
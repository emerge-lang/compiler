package compiler.reportings

import compiler.binding.BoundVariable

data class VisibilityNotAllowedOnVariableReporting(
    val variable: BoundVariable
) : Reporting(
    Level.ERROR,
    "${variable.kind}s cannot have a visibility",
    variable.declaration.visibility?.sourceLocation ?: variable.declaration.sourceLocation,
) {
    override fun toString() = super.toString()
}
package compiler.diagnostic

import compiler.binding.BoundVariable

data class VisibilityNotAllowedOnVariableDiagnostic(
    val variable: BoundVariable
) : Diagnostic(
    Level.ERROR,
    "${variable.kind}s cannot have a visibility",
    variable.declaration.visibility?.sourceLocation ?: variable.declaration.span,
) {
    override fun toString() = super.toString()
}
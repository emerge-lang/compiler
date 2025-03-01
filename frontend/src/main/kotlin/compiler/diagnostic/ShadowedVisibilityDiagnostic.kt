package compiler.diagnostic

import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility

class ShadowedVisibilityDiagnostic(
    val element: DefinitionWithVisibility,
    val contextVisibility: BoundVisibility,
) : Diagnostic(
    Level.WARNING,
    "This visibility has no effect because the enclosing context is $contextVisibility",
    element.visibility.astNode.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ShadowedVisibilityDiagnostic) return false

        if (element != other.element) return false

        return true
    }

    override fun hashCode(): Int {
        return element.hashCode()
    }
}
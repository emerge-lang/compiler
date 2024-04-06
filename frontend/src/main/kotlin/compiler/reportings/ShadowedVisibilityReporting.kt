package textutils.compiler.reportings

import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.reportings.Reporting

class ShadowedVisibilityReporting(
    val element: DefinitionWithVisibility,
    val contextVisibility: BoundVisibility,
) : Reporting(
    Level.WARNING,
    "This visibility has no effect because the enclosing context is $contextVisibility",
    element.visibility.astNode.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ShadowedVisibilityReporting) return false

        if (element != other.element) return false

        return true
    }

    override fun hashCode(): Int {
        return element.hashCode()
    }
}
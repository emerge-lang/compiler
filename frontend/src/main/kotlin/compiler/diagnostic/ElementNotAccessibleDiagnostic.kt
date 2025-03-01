package compiler.diagnostic

import compiler.binding.BoundVisibility
import compiler.binding.DefinitionWithVisibility
import compiler.lexer.Span

class ElementNotAccessibleDiagnostic(
    val element: DefinitionWithVisibility,
    val visibility: BoundVisibility,
    val accessAt: Span
) : Diagnostic(
    Level.ERROR,
    run {
        "${element.toStringForErrorMessage()} is $visibility, cannot be accessed from ${accessAt.sourceFile.packageName}"
    },
    accessAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ElementNotAccessibleDiagnostic) return false

        if (element !== other.element) return false
        if (accessAt != other.accessAt) return false

        return true
    }

    override fun hashCode(): Int {
        var result = System.identityHashCode(element)
        result = 31 * result + accessAt.hashCode()
        return result
    }
}
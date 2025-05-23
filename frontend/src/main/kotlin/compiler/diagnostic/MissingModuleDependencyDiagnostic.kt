package compiler.diagnostic

import compiler.binding.DefinitionWithVisibility
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class MissingModuleDependencyDiagnostic(
    val element: DefinitionWithVisibility,
    accessAt: Span,
    val moduleOfAccessedElement: CanonicalElementName.Package,
    val moduleOfAccess: CanonicalElementName.Package,
) : Diagnostic(
    Severity.ERROR,
    "Module $moduleOfAccess cannot access ${element.toStringForErrorMessage()} because it doesn't declare a dependency on module $moduleOfAccessedElement. Declare that dependency (in the bazel script).",
    accessAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other === this) return true
        if (other !is MissingModuleDependencyDiagnostic) return false

        if (this.moduleOfAccess != other.moduleOfAccess) return false
        if (this.moduleOfAccessedElement != other.moduleOfAccessedElement) return false

        return true
    }

    override fun hashCode(): Int {
        var result = MissingModuleDependencyDiagnostic::class.java.hashCode()
        result = 31 * result + moduleOfAccessedElement.hashCode()
        result = 31 * result + moduleOfAccess.hashCode()
        return result
    }
}
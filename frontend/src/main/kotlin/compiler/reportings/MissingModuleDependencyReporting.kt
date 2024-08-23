package compiler.reportings

import compiler.binding.DefinitionWithVisibility
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class MissingModuleDependencyReporting(
    val element: DefinitionWithVisibility,
    accessAt: Span,
    val moduleOfAccessedElement: CanonicalElementName.Package,
    val moduleOfAccess: CanonicalElementName.Package,
) : Reporting(
    Level.ERROR,
    "Module $moduleOfAccess cannot access ${element.toStringForErrorMessage()} because it doesn't declare a dependency on module $moduleOfAccessedElement. Declare that dependency (this should be done by your build tool, really).",
    accessAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other === this) return true
        if (other !is MissingModuleDependencyReporting) return false

        if (this.moduleOfAccess != other.moduleOfAccess) return false
        if (this.moduleOfAccessedElement != other.moduleOfAccessedElement) return false

        return true
    }

    override fun hashCode(): Int {
        var result = MissingModuleDependencyReporting::class.java.hashCode()
        result = 31 * result + moduleOfAccessedElement.hashCode()
        result = 31 * result + moduleOfAccess.hashCode()
        return result
    }
}
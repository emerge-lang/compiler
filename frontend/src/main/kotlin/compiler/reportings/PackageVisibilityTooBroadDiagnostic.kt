package compiler.reportings

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class PackageVisibilityTooBroadDiagnostic(
    val owningModule: CanonicalElementName.Package,
    val declaredPackageVisibility: CanonicalElementName.Package,
    span: Span,
) : Diagnostic(
    Level.ERROR,
    "Visibility can only be limited inside the module. Outside visibility must be export.\n"
            + "Cannot broaden visibility to package $declaredPackageVisibility outside of the own module $owningModule",
    span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is PackageVisibilityTooBroadDiagnostic) return false

        if (super.span != other.span) return false
        if (declaredPackageVisibility != other.declaredPackageVisibility) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.span.hashCode()
        result = 31 * result + declaredPackageVisibility.hashCode()
        return result
    }
}
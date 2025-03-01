package compiler.diagnostic

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

data class UnresolvablePackageNameDiagnostic(
    val name: CanonicalElementName.Package,
    val location: Span
) : Diagnostic(
    Level.ERROR,
    "Package $name could not be found",
    location,
) {
    override fun toString() = super.toString()
}
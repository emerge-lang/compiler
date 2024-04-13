package compiler.reportings

import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

data class UnresolvablePackageNameReporting(
    val name: CanonicalElementName.Package,
    val location: SourceLocation
) : Reporting(
    Level.ERROR,
    "Package $name could not be found",
    location,
) {
    override fun toString() = super.toString()
}
package compiler.reportings

import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.PackageName

data class UnresolvablePackageNameReporting(
    val name: PackageName,
    val location: SourceLocation
) : Reporting(
    Level.ERROR,
    "Package $name could not be found",
    location,
) {
    override fun toString() = super.toString()
}
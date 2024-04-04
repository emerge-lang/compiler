package compiler.reportings

import compiler.lexer.SourceLocation
import io.github.tmarsteel.emerge.backend.api.DotName

class PackageVisibilityTooBroadReporting(
    val owningModule: DotName,
    val declaredPackageVisibility: DotName,
    sourceLocation: SourceLocation,
) : Reporting(
    Level.ERROR,
    "Visibilit can only be limited inside the module. Outside visibility must be export.\n"
            + "Cannot broaden visibility to package $declaredPackageVisibility outside of the own module $owningModule",
    sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is PackageVisibilityTooBroadReporting) return false

        if (super.sourceLocation != other.sourceLocation) return false
        if (declaredPackageVisibility != other.declaredPackageVisibility) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.sourceLocation.hashCode()
        result = 31 * result + declaredPackageVisibility.hashCode()
        return result
    }
}
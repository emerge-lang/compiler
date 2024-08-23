package compiler.reportings

import compiler.ast.BaseTypeDeclaration
import io.github.tmarsteel.emerge.common.CanonicalElementName

class DuplicateBaseTypesReporting(
    val packageName: CanonicalElementName.Package,
    val duplicates: List<BaseTypeDeclaration>,
) : Reporting(
    Level.ERROR,
    "Package $packageName declares multiple types with name ${duplicates.first().name.value}",
    duplicates.first().declaredAt,
) {
    private val simpleName = duplicates.first().name.value

    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateSourceLocations(duplicates.map { it.declaredAt })
        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DuplicateBaseTypesReporting) return false
        if (!super.equals(other)) return false

        if (packageName != other.packageName) return false
        if (simpleName != other.simpleName) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + packageName.hashCode()
        result = 31 * result + simpleName.hashCode()
        return result
    }

}
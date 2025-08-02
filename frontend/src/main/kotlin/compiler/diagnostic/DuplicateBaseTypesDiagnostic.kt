package compiler.diagnostic

import compiler.ast.BaseTypeDeclaration
import compiler.diagnostic.rendering.CellBuilder
import io.github.tmarsteel.emerge.common.CanonicalElementName

class DuplicateBaseTypesDiagnostic(
    val packageName: CanonicalElementName.Package,
    val duplicates: List<BaseTypeDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    "Package $packageName declares multiple types with name ${duplicates.first().name.value}",
    duplicates.first().declaredAt,
) {
    private val simpleName = duplicates.first().name.value

    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(duplicates.map { SourceHint(it.declaredAt, severity = severity) })
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is DuplicateBaseTypesDiagnostic) return false
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
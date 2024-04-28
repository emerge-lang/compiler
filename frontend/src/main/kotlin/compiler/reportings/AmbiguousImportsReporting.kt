package compiler.reportings

import compiler.ast.ImportDeclaration

data class AmbiguousImportsReporting(
    val imports: List<ImportDeclaration>,
    val commonSimpleName: String,
) : Reporting(
    Level.ERROR,
    "These imports are ambiguous, they all import the symbol $commonSimpleName",
    imports.first().declaredAt,
) {
    override fun toString() = "$levelAndMessage\n${illustrateSourceLocations(imports.map { it.declaredAt })}"
}
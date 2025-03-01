package compiler.diagnostic

import compiler.ast.ImportDeclaration

data class AmbiguousImportsDiagnostic(
    val imports: List<ImportDeclaration>,
    val commonSimpleName: String,
) : Diagnostic(
    Level.ERROR,
    "These imports are ambiguous, they all import the symbol $commonSimpleName",
    imports.first().declaredAt,
) {
    override fun toString() = "$levelAndMessage\n${illustrateSourceLocations(imports.map { it.declaredAt })}"
}
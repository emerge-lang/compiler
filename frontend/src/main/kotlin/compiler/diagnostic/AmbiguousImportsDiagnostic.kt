package compiler.diagnostic

import compiler.ast.ImportDeclaration
import compiler.diagnostic.rendering.CellBuilder

data class AmbiguousImportsDiagnostic(
    val imports: List<ImportDeclaration>,
    val commonSimpleName: String,
) : Diagnostic(
    Severity.ERROR,
    "These imports are ambiguous, they all import the symbol $commonSimpleName",
    imports.first().declaredAt,
) {
    context(CellBuilder)
    override fun renderBody() {
        sourceHints(*imports.map { SourceHint(it.declaredAt, null, severity = severity) }.toTypedArray())
    }
}
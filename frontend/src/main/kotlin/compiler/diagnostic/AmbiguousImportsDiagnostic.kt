package compiler.diagnostic

import compiler.ast.ImportDeclaration
import compiler.diagnostic.rendering.MonospaceCanvas
import compiler.diagnostic.rendering.SourceQuoteWidget

data class AmbiguousImportsDiagnostic(
    val imports: List<ImportDeclaration>,
    val commonSimpleName: String,
) : Diagnostic(
    Severity.ERROR,
    "These imports are ambiguous, they all import the symbol $commonSimpleName",
    imports.first().declaredAt,
) {
    override fun render(canvas: MonospaceCanvas) {
        renderLevelAndMessage(canvas)
        SourceQuoteWidget.renderHintsFromMultipleFiles(canvas, *imports.map { it.declaredAt }.toTypedArray())
    }
}
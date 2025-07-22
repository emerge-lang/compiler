package compiler.diagnostic

import compiler.ast.AstImportDeclaration
import compiler.diagnostic.rendering.CellBuilder

data class RedundantImportsDiagnostic(
    val imports: List<AstImportDeclaration>,
    val commonSimpleName: String,
) : Diagnostic(
    Severity.INFO,
    "These imports are redundant, they all import the same element ${commonSimpleName.quoteIdentifier()}",
    imports.first().declaredAt,
) {
    context(CellBuilder)
    override fun renderBody() {
        sourceHints(*imports.flatMap { import ->
            import.symbols
                .filter { it.value == commonSimpleName }
                .map { SourceHint(it.span, null, severity = severity) }
        }.toTypedArray())
    }
}
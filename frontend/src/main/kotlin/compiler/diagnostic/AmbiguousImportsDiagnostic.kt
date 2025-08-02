package compiler.diagnostic

import compiler.ast.AstImportDeclaration
import compiler.diagnostic.rendering.CellBuilder

data class AmbiguousImportsDiagnostic(
    val imports: List<AstImportDeclaration>,
    val commonSimpleName: String,
) : Diagnostic(
    Severity.ERROR,
    "These imports are ambiguous, they all import the symbol ${commonSimpleName.quoteIdentifier()}",
    imports.first().declaredAt,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(*imports.flatMap { import ->
                import.symbols
                    .filter { it.value == commonSimpleName }
                    .map { SourceHint(it.span, null, severity = severity) }
            }.toTypedArray())
        }
    }
}
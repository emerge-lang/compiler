package compiler.diagnostic

import compiler.ast.BaseTypeDestructorDeclaration
import compiler.diagnostic.rendering.CellBuilder

data class MultipleClassDestructorsDiagnostic(
    val additionalDestructors: Collection<BaseTypeDestructorDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    "Classes can have only one destructor. These must be removed",
    additionalDestructors.first().span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(additionalDestructors.map { SourceHint(it.span, severity = severity) })
    }
}
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
    context(CellBuilder) override fun renderBody() {
        sourceHints(additionalDestructors.map { SourceHint(it.span, severity = severity) })
    }
}
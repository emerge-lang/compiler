package compiler.diagnostic

import compiler.ast.BaseTypeConstructorDeclaration
import compiler.diagnostic.rendering.CellBuilder

data class MultipleClassConstructorsDiagnostic(
    val additionalConstructors: Collection<BaseTypeConstructorDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    "Classes can have only one constructor. These must be removed",
    additionalConstructors.first().span,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(additionalConstructors.map { SourceHint(it.span, severity = severity) })
        }
    }
}
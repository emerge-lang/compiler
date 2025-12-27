package compiler.diagnostic

import compiler.ast.AstBaseTypeMemberVariableAttribute
import compiler.diagnostic.rendering.CellBuilder

class ConflictingBaseTypeMemberVariableAttributesDiagnostic(
    val attributesInConflict: List<AstBaseTypeMemberVariableAttribute>,
) : Diagnostic(
    Severity.ERROR,
    "These attributes contradict each other",
    attributesInConflict.first().attributeName.span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(*attributesInConflict.map { SourceHint(it.attributeName.span, severity = severity) }.toTypedArray())
    }
}
package compiler.diagnostic

import compiler.ast.AstBaseTypeMemberVariableAttribute
import compiler.diagnostic.rendering.CellBuilder

class DuplicateMemberVariableAttributeDiagnostic(
    val duplicates: List<AstBaseTypeMemberVariableAttribute>,
) : Diagnostic(
    Severity.WARNING,
    "Duplicate member variable attribute ${duplicates.first().attributeName.keyword.text}",
    duplicates.first().attributeName.span,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(duplicates.map { SourceHint(it.attributeName.span, severity = severity) })
        }
    }
}
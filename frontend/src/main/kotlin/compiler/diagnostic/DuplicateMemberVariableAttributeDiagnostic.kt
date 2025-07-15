package compiler.diagnostic

import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.KeywordToken

class DuplicateMemberVariableAttributeDiagnostic(
    val duplicates: List<KeywordToken>,
) : Diagnostic(
    Severity.WARNING,
    "Duplicate member variable attribute ${duplicates.first().keyword.text}",
    duplicates.first().span,
) {
    context(CellBuilder)
    override fun renderBody() {
        sourceHints(duplicates.map { SourceHint(it.span, severity = severity) })
    }
}
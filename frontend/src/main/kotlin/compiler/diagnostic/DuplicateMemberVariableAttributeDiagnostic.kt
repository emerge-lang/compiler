package compiler.diagnostic

import compiler.lexer.KeywordToken

class DuplicateMemberVariableAttributeDiagnostic(
    val duplicates: List<KeywordToken>,
) : Diagnostic(
    Severity.WARNING,
    "Duplicate member variable attribute ${duplicates.first().keyword.text}",
    duplicates.first().span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateSourceLocations(duplicates.map { it.span })}"
}
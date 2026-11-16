package compiler.diagnostic

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken

class MissingElseBranchDiagnostic(
    val keyword: KeywordToken,
) : Diagnostic(
    Severity.ERROR,
    "This `${keyword.keyword.text}` is used as a value, it needs an `${Keyword.ELSE.text}` branch",
    keyword.span,
) {
    override fun toString() = super.toString()
}

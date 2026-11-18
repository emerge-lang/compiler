package compiler.diagnostic

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken

/**
 * The branches of a `when` already cover all the values of its subject, so its `else` branch is never executed.
 */
class UnreachableWhenElseBranchDiagnostic(
    val elseKeyword: KeywordToken,
) : Diagnostic(
    Severity.WARNING,
    "The other branches of this `${Keyword.WHEN.text}` cover all possible values, this `${Keyword.ELSE.text}` branch is never executed",
    elseKeyword.span,
) {
    override fun toString() = super.toString()
}

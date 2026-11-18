package compiler.diagnostic

import compiler.ast.AstWhenExpression
import compiler.lexer.Keyword

class WhenBranchNeedsSubjectDiagnostic(
    val branch: AstWhenExpression.Branch,
) : Diagnostic(
    Severity.ERROR,
    "This branch needs a subject, but the enclosing ${Keyword.WHEN.text} doesn't declare one",
    branch.condition.span,
)
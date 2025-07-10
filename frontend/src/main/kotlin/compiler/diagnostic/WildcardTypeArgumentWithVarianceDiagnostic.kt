package compiler.diagnostic

import compiler.ast.type.AstTypeArgument
import compiler.lexer.Span

class WildcardTypeArgumentWithVarianceDiagnostic(
    val erroneousArg: AstTypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Variance is not supported on wildcard type arguments",
    erroneousArg.span ?: Span.UNKNOWN
)
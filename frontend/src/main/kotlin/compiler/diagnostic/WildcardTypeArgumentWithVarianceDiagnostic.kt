package compiler.diagnostic

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

class WildcardTypeArgumentWithVarianceDiagnostic(
    val erroneousArg: TypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Variance is not supported on wildcard type arguments",
    erroneousArg.span ?: Span.UNKNOWN
)
package compiler.diagnostic

import compiler.ast.type.AstTypeArgument
import compiler.lexer.Span

class WildcardTypeArgumentOnInvocationDiagnostic(
    val argument: AstTypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Wildcard type arguments are not supported on function invocations",
    argument.span ?: Span.UNKNOWN,
)
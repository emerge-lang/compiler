package compiler.diagnostic

import compiler.ast.type.TypeArgument
import compiler.lexer.Span

class WildcardTypeArgumentOnInvocationDiagnostic(
    val argument: TypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Wildcard type arguments are not supported on function invocations",
    argument.span ?: Span.UNKNOWN,
)
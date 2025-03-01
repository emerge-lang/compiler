package compiler.diagnostic

import compiler.lexer.Span

class ConstructorDeclaredNothrowDiagnostic(
    declaredNothrowAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "Constructors cannot be declared nothrow. Constructors allocate memory, which can always fail when the executing machine is out of memory.",
    declaredNothrowAt,
)
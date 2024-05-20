package compiler.reportings

import compiler.lexer.Span

class ConstructorDeclaredNothrowReporting(
    declaredNothrowAt: Span,
) : Reporting(
    Level.ERROR,
    "Constructors cannot be declared nothrow. Constructors allocate memory, which can always fail when the executing machine is out of memory.",
    declaredNothrowAt,
)
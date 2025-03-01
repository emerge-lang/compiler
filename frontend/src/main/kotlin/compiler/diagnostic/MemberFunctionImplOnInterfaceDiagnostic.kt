package compiler.diagnostic

import compiler.lexer.Span

data class MemberFunctionImplOnInterfaceDiagnostic(
    val memberFunctionBodyLocation: Span,
) : Diagnostic(
    Severity.ERROR,
    "Interfaces cannot define implementations for member functions. Move this implementation to a class and mix that in where needed.",
    memberFunctionBodyLocation,
)
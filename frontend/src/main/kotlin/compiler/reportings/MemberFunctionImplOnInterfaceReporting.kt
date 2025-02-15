package compiler.reportings

import compiler.lexer.Span

data class MemberFunctionImplOnInterfaceReporting(
    val memberFunctionBodyLocation: Span,
) : Reporting(
    Level.ERROR,
    "Interfaces cannot define implementations for member functions. Move this implementation to a class and mix that in where needed.",
    memberFunctionBodyLocation,
)
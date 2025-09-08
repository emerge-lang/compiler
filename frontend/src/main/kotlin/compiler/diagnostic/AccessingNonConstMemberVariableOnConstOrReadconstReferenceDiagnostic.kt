package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

class AccessingNonConstMemberVariableOnConstOrReadconstReferenceDiagnostic(
    val nonConstMember: BaseTypeMemberVariableDeclaration,
    accessAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "The member variable ${nonConstMember.name.quote()} is not guaranteed to be immutable, so it cannot be accessed through a const reference",
    accessAt,
)
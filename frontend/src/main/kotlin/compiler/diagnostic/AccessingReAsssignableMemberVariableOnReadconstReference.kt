package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

class AccessingReAsssignableMemberVariableOnReadconstReference(
    val member: BaseTypeMemberVariableDeclaration,
    accessAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "Member variable ${member.name.quote()} is re-assignable, so it may change between multiple accesses. Hence, reading it through a readconst reference is not allowed.",
    accessAt,
)
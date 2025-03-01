package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

data class UseOfUninitializedClassMemberVariableDiagnostic(
    val member: BaseTypeMemberVariableDeclaration,
    val usedAt: Span,
) : Diagnostic(
    Severity.ERROR,
    run {
        if (member.variableDeclaration.isReAssignable) {
            "Member variable ${member.name.value} might not have been initialized yet"
        } else {
            "Member variable ${member.name.value} has not been initialized yet"
        }
    },
    usedAt,
) {
    override fun toString() = super.toString()
}
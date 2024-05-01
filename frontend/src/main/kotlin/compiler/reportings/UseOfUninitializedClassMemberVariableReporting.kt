package compiler.reportings

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

data class UseOfUninitializedClassMemberVariableReporting(
    val member: BaseTypeMemberVariableDeclaration,
    val usedAt: Span,
) : Reporting(
    Level.ERROR,
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
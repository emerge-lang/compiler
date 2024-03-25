package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration
import compiler.lexer.SourceLocation

data class UseOfUninitializedClassMemberVariableReporting(
    val member: ClassMemberVariableDeclaration,
    val usedAt: SourceLocation,
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
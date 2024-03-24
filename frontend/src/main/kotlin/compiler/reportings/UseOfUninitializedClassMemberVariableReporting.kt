package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration
import compiler.lexer.SourceLocation

data class UseOfUninitializedClassMemberVariableReporting(
    val member: ClassMemberVariableDeclaration,
    val usedAt: SourceLocation,
) : Reporting(
    Level.ERROR,
    "Member variable ${member.name.value} might not have been initialized yet",
    usedAt,
) {
    override fun toString() = super.toString()
}
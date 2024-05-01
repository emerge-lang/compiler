package compiler.reportings

import compiler.ast.BaseTypeMemberVariableDeclaration

class ClassMemberVariableNotInitializedDuringObjectConstructionReporting(
    val memberDeclaration: BaseTypeMemberVariableDeclaration
) : Reporting(
    Level.ERROR,
    "Member variable ${memberDeclaration.name.value} is not guaranteed to be initialized during object construction",
    memberDeclaration.span,
) {
    override fun equals(other: Any?): Boolean {
        if (other !is ClassMemberVariableNotInitializedDuringObjectConstructionReporting) {
            return false
        }

        return other.span == this.span
    }

    override fun hashCode(): Int {
        return span.hashCode()
    }
}
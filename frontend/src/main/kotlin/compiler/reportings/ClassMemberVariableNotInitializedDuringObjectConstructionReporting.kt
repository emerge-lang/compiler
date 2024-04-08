package compiler.reportings

import compiler.ast.BaseTypeMemberVariableDeclaration

class ClassMemberVariableNotInitializedDuringObjectConstructionReporting(
    val memberDeclaration: BaseTypeMemberVariableDeclaration
) : Reporting(
    Level.ERROR,
    "Member variable ${memberDeclaration.name.value} is not guaranteed to be initialized during object construction",
    memberDeclaration.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other !is ClassMemberVariableNotInitializedDuringObjectConstructionReporting) {
            return false
        }

        return other.sourceLocation == this.sourceLocation
    }

    override fun hashCode(): Int {
        return sourceLocation.hashCode()
    }
}
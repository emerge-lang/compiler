package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration

class ClassMemberVariableNotInitializedDuringObjectConstructionReporting(
    val memberDeclaration: ClassMemberVariableDeclaration
) : Reporting(
    Level.ERROR,
    "Member variable ${memberDeclaration.name.value} is not guaranteed to be during object construction",
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
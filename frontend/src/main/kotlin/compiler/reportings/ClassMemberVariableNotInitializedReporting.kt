package compiler.reportings

import compiler.ast.ClassMemberVariableDeclaration

class ClassMemberVariableNotInitializedReporting(
    val memberDeclaration: ClassMemberVariableDeclaration
) : Reporting(
    Level.ERROR,
    "Member variable ${memberDeclaration.name.value} must be initialized",
    memberDeclaration.declaredAt,
) {
    override fun equals(other: Any?): Boolean {
        if (other !is ClassMemberVariableNotInitializedReporting) {
            return false
        }

        return other.sourceLocation == this.sourceLocation
    }

    override fun hashCode(): Int {
        return sourceLocation.hashCode()
    }
}
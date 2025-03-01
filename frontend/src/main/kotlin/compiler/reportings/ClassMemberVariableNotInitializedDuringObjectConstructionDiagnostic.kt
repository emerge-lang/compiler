package compiler.reportings

import compiler.ast.BaseTypeMemberVariableDeclaration

class ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic(
    val memberDeclaration: BaseTypeMemberVariableDeclaration
) : Diagnostic(
    Level.ERROR,
    "Member variable ${memberDeclaration.name.value} is not guaranteed to be initialized during object construction",
    memberDeclaration.span,
) {
    override fun equals(other: Any?): Boolean {
        if (other !is ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic) {
            return false
        }

        return other.span == this.span
    }

    override fun hashCode(): Int {
        return span.hashCode()
    }
}
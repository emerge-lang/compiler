package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration

class ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic(
    val memberDeclaration: BaseTypeMemberVariableDeclaration
) : Diagnostic(
    Severity.ERROR,
        "Member variable ${memberDeclaration.name.quote()} is not guaranteed to be initialized during object construction",
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
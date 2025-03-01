package compiler.reportings

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.lexer.Span

class NotAllMemberVariablesInitializedDiagnostic(
    val uninitializedMembers: Collection<BaseTypeMemberVariableDeclaration>,
    span: Span,
) : Diagnostic(
    Level.ERROR,
    run {
        val memberList = uninitializedMembers.joinToString(transform = { "- ${it.name.value}" }, separator = "\n")
        "The object is not fully initialized yet. These member variables must be initialized before the object can be used regularly:\n$memberList"
    },
    span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is NotAllMemberVariablesInitializedDiagnostic) return false

        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        return span.hashCode()
    }
}
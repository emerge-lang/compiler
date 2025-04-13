package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.binding.AccessorKind

class MultipleAccessorsForVirtualMemberVariableDiagnostic(
    val memberVarName: String,
    val kind: AccessorKind,
    val accessorsOfSameKind: List<FunctionDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    run {
        val kindStr = when (kind) {
            AccessorKind.READ -> "getters"
            AccessorKind.WRITE -> "setters"
        }
        "Multiple $kindStr defined for virtual member variable `$memberVarName`"
    },
    accessorsOfSameKind.map { it.declaredAt}.minBy { it.fromLineNumber },
) {
    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + memberVarName.hashCode()
        result = 31 * result + kind.hashCode()
        result = 31 * result + span.hashCode()

        return result
    }

    override fun equals(other: Any?): Boolean {
        if (other !is MultipleAccessorsForVirtualMemberVariableDiagnostic) return false

        if (this.memberVarName != other.memberVarName) return false
        if (this.kind != other.kind) return false
        if (this.span != other.span) return false

        return true
    }

    override fun toString() = "$levelAndMessage\n${illustrateHints(accessorsOfSameKind.map {
        SourceHint(it.declaredAt, null)
    })}"
}
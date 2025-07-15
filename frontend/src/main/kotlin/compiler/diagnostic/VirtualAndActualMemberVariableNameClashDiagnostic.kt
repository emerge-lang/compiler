package compiler.diagnostic

import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.binding.BoundMemberFunction
import compiler.diagnostic.rendering.CellBuilder

class VirtualAndActualMemberVariableNameClashDiagnostic(
    val memberVar: BaseTypeMemberVariableDeclaration,
    clashingAccessors: List<BoundMemberFunction>,
) : Diagnostic(
    Severity.ERROR,
    "Member variable `${memberVar.name.value}` is defined both in terms of a field and in terms of accessors. Choose either a field or accessor functions.",
    memberVar.span,
) {
    private val accessorsDeclarationHints = clashingAccessors.map {
        SourceHint(it.declaredAt, "an accessor is declared here", false)
    }

    context(CellBuilder)
    override fun renderBody() {
        sourceHints(
            listOf(SourceHint(memberVar.span, "member variable declared as a field here", true, severity = Severity.INFO)) + accessorsDeclarationHints
        )
    }
}
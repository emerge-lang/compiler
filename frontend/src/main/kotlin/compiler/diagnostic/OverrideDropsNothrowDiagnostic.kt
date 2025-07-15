package compiler.diagnostic

import compiler.binding.BoundMemberFunction
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Keyword

data class OverrideDropsNothrowDiagnostic(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Diagnostic(
    Severity.ERROR,
    "Function ${override.canonicalName} must be declared ${Keyword.NOTHROW.text}, because it is overriding a function that is also declared nothrow.",
    override.declaredAt,
) {
    context(CellBuilder) override fun renderBody() {
        sourceHints(
            SourceHint(override.declaredAt, "override is not declared ${Keyword.NOTHROW.text}", severity = severity),
            SourceHint(superFunction.attributes.firstNothrowAttribute!!.sourceLocation, "overridden function is declared ${Keyword.NOTHROW.text} here"),
        )
    }
}
package compiler.diagnostic

import compiler.binding.BoundFunction
import compiler.binding.BoundMemberFunction
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

data class OverrideAddsSideEffectsDiagnostic(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Diagnostic(
    Severity.ERROR,
    "The purity of overrides must be compatible with that of the overridden function. ${override.purity} is not a subset of ${superFunction.purity}",
    override.declaredAt,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(
            SourceHint(superFunction.purityDeclarationLocation, "overridden function is ${superFunction.purity}", severity = Severity.INFO),
            SourceHint(override.purityDeclarationLocation, "override is ${override.purity}", severity = severity),
        )
    }
}

private val BoundFunction.purityDeclarationLocation: Span
    get() = attributes.purityAttribute?.sourceLocation ?: declaredAt
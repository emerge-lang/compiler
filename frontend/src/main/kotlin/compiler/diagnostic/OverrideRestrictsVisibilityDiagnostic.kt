package compiler.diagnostic

import compiler.binding.BoundFunction
import compiler.binding.BoundMemberFunction
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.MemoryLexerSourceFile
import compiler.lexer.Span

data class OverrideRestrictsVisibilityDiagnostic(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Diagnostic(
    Severity.ERROR,
    "The visibility of overrides must be the same or broader than that of the overridden function.",
    override.declaredAt,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(
            SourceHint(superFunction.visibilityLocation, "overridden function is ${superFunction.visibility}"),
            SourceHint(override.visibilityLocation, "override is ${override.visibility}"),
        )
    }
}

private val BoundFunction.visibilityLocation: Span
    get() = visibility.astNode.sourceLocation.takeUnless { it.sourceFile is MemoryLexerSourceFile && it.sourceFile.name == "UNKNOWN" }
        ?: declaredAt
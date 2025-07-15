package compiler.diagnostic

import compiler.ast.AstMixinStatement
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

class ObjectUsedBeforeMixinInitializationDiagnostic(
    val uninitializedMixin: AstMixinStatement,
    objectUsedAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "The object is not fully initialized yet. A mixin must still be initialized.",
    objectUsedAt,
) {
    context(CellBuilder) override fun renderBody() {
        sourceHints(
            SourceHint(span, "Object used before initialization is complete", severity = severity),
            SourceHint(uninitializedMixin.span, "This mixin is not yet initialized", severity = Severity.INFO),
        )
    }
}
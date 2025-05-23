package compiler.diagnostic

import compiler.ast.AstMixinStatement
import compiler.lexer.Span

class ObjectUsedBeforeMixinInitializationDiagnostic(
    val uninitializedMixin: AstMixinStatement,
    objectUsedAt: Span,
) : Diagnostic(
    Severity.ERROR,
    "The object is not fully initialized yet. A mixin must still be initialized.",
    objectUsedAt,
) {
    override fun toString(): String {
        return "$levelAndMessage\n" + illustrateHints(listOf(
            SourceHint(span, "Object used before initialization is complete"),
            SourceHint(uninitializedMixin.span, "This mixin is not yet initialized")
        ))
    }
}
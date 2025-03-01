package compiler.diagnostic

import compiler.ast.AstMixinStatement

data class UnusedMixinDiagnostic(val stmt: AstMixinStatement) : Diagnostic(
    Severity.ERROR,
    "This mixin is not used; it doesn't apply to any of the inherited functions that aren't overridden.",
    stmt.span,
) {
    override fun toString() = super.toString()
}
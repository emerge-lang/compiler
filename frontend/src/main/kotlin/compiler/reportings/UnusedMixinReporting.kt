package compiler.reportings

import compiler.ast.AstMixinStatement

data class UnusedMixinReporting(val stmt: AstMixinStatement) : Reporting(
    Level.ERROR,
    "This mixin is not used; it doesn't apply to any of the inherited functions that aren't overridden.",
    stmt.span,
)
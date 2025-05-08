package compiler.diagnostic

import compiler.ast.type.AstUnionType

class SimplifyableUnionTypeDiagnostic(
    val complicatedType: AstUnionType,
    val simplerVersion: AstUnionType,
) : Diagnostic(
    Severity.WARNING,
    "This union type can be simplified",
    complicatedType.span,
) {
    override fun toString() = "$levelAndMessage\n  simpler alternative: $simplerVersion\nin $span"
}
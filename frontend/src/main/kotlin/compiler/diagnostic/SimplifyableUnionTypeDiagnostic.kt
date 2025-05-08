package compiler.diagnostic

import compiler.ast.type.AstUnionType
import compiler.binding.type.BoundTypeReference

class SimplifyableUnionTypeDiagnostic(
    val complicatedType: AstUnionType,
    val simplerVersion: BoundTypeReference,
) : Diagnostic(
    Severity.WARNING,
    "This union type can be simplified",
    complicatedType.span,
) {
    override fun toString() = "$levelAndMessage\n  simpler alternative: $simplerVersion\nin $span"
}
package compiler.diagnostic

import compiler.ast.type.AstIntersectionType
import compiler.binding.type.BoundTypeReference

class SimplifiableIntersectionTypeDiagnostic(
    val complicatedType: AstIntersectionType,
    val simplerVersion: BoundTypeReference,
) : Diagnostic(
    Severity.WARNING,
    "This intersection-type can be simplified",
    complicatedType.span,
) {
    override fun toString() = "$levelAndMessage\n  simpler alternative: $simplerVersion\nin $span"
}
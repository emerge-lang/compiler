package compiler.diagnostic

import compiler.ast.type.AstIntersectionType
import compiler.binding.type.BoundTypeReference

class SimplifiableIntersectionTypeDiagnostic(
    val complicatedType: AstIntersectionType,
    val simplerVersion: BoundTypeReference,
) : Diagnostic(
    Severity.WARNING,
    if (simplerVersion.isNothing) "It is impossible to construct a value that satisfies this type" else "This intersection-type can be simplified",
    complicatedType.span,
) {
    override fun toString() = if (simplerVersion.isNothing) {
        super.toString()
    } else {
        "$levelAndMessage  simpler alternative: $simplerVersion\n\nin $span"
    }
}
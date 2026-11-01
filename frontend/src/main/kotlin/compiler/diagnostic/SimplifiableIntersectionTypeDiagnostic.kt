package compiler.diagnostic

import compiler.ast.type.AstIntersectionType
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.rendering.CellBuilder
import compiler.diagnostic.rendering.TextSpan

class SimplifiableIntersectionTypeDiagnostic(
    val complicatedType: AstIntersectionType,
    val simplerVersion: BoundTypeReference,
) : Diagnostic(
    Severity.WARNING,
    if (simplerVersion.isNonNullableNothing) "It is impossible to construct a value that satisfies this type" else "This intersection-type can be simplified",
    complicatedType.span,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            if (!simplerVersion.isNonNullableNothing) {
                append(TextSpan("simpler alternative: "))
                append(simplerVersion.quote())
                appendLineBreak()
            }

            super.renderBody()
        }
    }
}
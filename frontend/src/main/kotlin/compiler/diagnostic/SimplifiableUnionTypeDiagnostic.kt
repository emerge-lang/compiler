package compiler.diagnostic

import compiler.ast.type.AstUnionType
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.rendering.CellBuilder
import compiler.diagnostic.rendering.TextSpan

class SimplifiableUnionTypeDiagnostic(
    val complicatedType: AstUnionType,
    val simplerVersion: BoundTypeReference,
) : Diagnostic(
    Severity.WARNING,
    "This union-type can be simplified",
    complicatedType.span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        with(builder) {
            append(TextSpan("simpler alternative: "))
            append(simplerVersion.quote())
            appendLineBreak()

            super.renderBody()
        }
    }
}

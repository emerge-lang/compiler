package compiler.diagnostic

import compiler.ast.AstAnnotation
import compiler.ast.BaseTypeMemberVariableDeclaration
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

class InvalidAnnotationMemberDiagnostic(
    val member: BaseTypeMemberVariableDeclaration,
    val annotatableAnnotation: AstAnnotation,
    reason: String,
    spanOverride: Span?,
) : Diagnostic(
    Severity.ERROR,
    "This member variable cannot be stored in an annotation: $reason",
    spanOverride ?: member.variableDeclaration.type?.span ?: member.span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        with(builder) {
            sourceHints(
                SourceHint(annotatableAnnotation.span, "class marked as an annotation here"),
                SourceHint(span, severity = severity, description = "mutability declared here"),
            )
        }
    }
}
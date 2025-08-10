package compiler.diagnostic

import compiler.ast.type.AstSimpleTypeReference
import compiler.diagnostic.rendering.CellBuilder
import compiler.diagnostic.rendering.TextSpan
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class AmbiguousTypeReferenceDiagnostic(
    val reference: AstSimpleTypeReference,
    val candidates: List<CanonicalElementName.BaseType>,
    fileHasAmbiguousImportForSimpleName: Boolean,
) : Diagnostic(
    if (fileHasAmbiguousImportForSimpleName) Severity.CONSECUTIVE else Severity.ERROR,
    "This reference is ambiguous, there are multiple types in scope with simple name ${reference.simpleName.quoteIdentifier()}",
    reference.span ?: Span.UNKNOWN,
) {
    context(builder: CellBuilder)    
    override fun renderMessage() {
        with(builder) {
            text(message)
            for (candidate in candidates) {
                assureOnBlankLine()
                append(TextSpan("- "))
                append(candidate.simpleName.quoteIdentifier())
            }
        }
    }
}
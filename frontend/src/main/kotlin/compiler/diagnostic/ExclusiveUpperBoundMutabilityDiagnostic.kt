package compiler.diagnostic

import compiler.ast.type.TypeMutability
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

class ExclusiveUpperBoundMutabilityDiagnostic(
    val baseTypeName: CanonicalElementName.BaseType,
    val conflictingSupertypeMutabilities: List<Pair<Span, TypeMutability>>,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    run {
        val typeDescr = if (conflictingSupertypeMutabilities.size == 1) conflictingSupertypeMutabilities.single().second.keyword.text else {
            val enumeration = conflictingSupertypeMutabilities.asSequence()
                .map { it.second }
                .distinct()
                .map { it.keyword.text }
                .enumerateNonEmpty()

            "$enumeration at the same time"
        }

        "It is impossible to have an instance of ${baseTypeName.simpleName.quote()} that is $typeDescr"
    },
    span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(*conflictingSupertypeMutabilities.map { (span, _) -> SourceHint(span, severity = severity) }.toTypedArray())
    }
}
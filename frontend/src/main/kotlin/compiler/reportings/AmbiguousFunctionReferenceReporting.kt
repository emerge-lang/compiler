package compiler.reportings

import compiler.ast.expression.AstTopLevelFunctionReference
import compiler.binding.BoundFunction

class AmbiguousFunctionReferenceReporting(
    val reference: AstTopLevelFunctionReference,
    val candidates: List<BoundFunction>
) : Reporting(
    Reporting.Level.ERROR,
    "Multiple overloads of ${candidates.first().name} apply to this reference. Currently, function references have to be unambiguous by solely the name.",
    reference.span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(
        SourceHint(reference.span, "this reference is ambiguous", true),
        *candidates.map { SourceHint(it.declaredAt, "this is a viable candidate", nLinesContext = 0u) }.toTypedArray(),
    )}"
}
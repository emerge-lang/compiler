package compiler.reportings

import compiler.lexer.Span

class DroppingReferenceToObjectWithThrowingDestructorReporting(
    /** just for deduping diagnostics */
    val reference: Any,
    val referenceDroppedOrDeclaredAt: Span,
    val boundary: SideEffectBoundary,
) : Reporting(
    Level.ERROR,
    "When this reference is dropped, the destructor may throw. This is not allowed in a nothrow context ($boundary).",
    referenceDroppedOrDeclaredAt,
)
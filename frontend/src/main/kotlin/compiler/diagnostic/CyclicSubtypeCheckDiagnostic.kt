package compiler.diagnostic

import compiler.binding.type.BoundTypeReference
import compiler.lexer.Span

/**
 * Reported when deciding whether [sourceType] is a subtype of [targetType] comes back to the very same question,
 * so the type checker can't come to an answer.
 */
class CyclicSubtypeCheckDiagnostic(
    val targetType: BoundTypeReference,
    val sourceType: BoundTypeReference,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Type checking is cyclic at this location and cannot complete.",
    span,
)

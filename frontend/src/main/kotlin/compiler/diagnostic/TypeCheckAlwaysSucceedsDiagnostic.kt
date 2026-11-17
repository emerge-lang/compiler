package compiler.diagnostic

import compiler.binding.type.BoundTypeReference
import compiler.lexer.Span

/**
 * An `is` or `as` on a value whose static type says already that it is of the type.
 */
class TypeCheckAlwaysSucceedsDiagnostic(
    val kind: TypeCheckKind,
    val typeOfValue: BoundTypeReference,
    val typeToCheck: BoundTypeReference,
    span: Span,
) : Diagnostic(
    Severity.WARNING,
    when (kind) {
        TypeCheckKind.INSTANCE_OF -> "This check is always true"
        TypeCheckKind.CAST,
        TypeCheckKind.SAFE_CAST -> "This cast is superfluous, it always succeeds"
    } + ": every value of type $typeOfValue is a $typeToCheck.",
    span,
)

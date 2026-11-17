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

/**
 * An `is` or `as` on a value whose static type says already that it is not of the type.
 *
 * A warning, not an error, on purpose: the logic that finds these (`staticResultOfTypeCheck`) goes beyond the
 * subtype relation and is not verified as strongly. Where it is wrong, the code still compiles, and the check at
 * runtime decides. A cast that strengthens the mutability is an error regardless ([ForbiddenCastDiagnostic]).
 */
class TypeCheckNeverSucceedsDiagnostic(
    val kind: TypeCheckKind,
    val typeOfValue: BoundTypeReference,
    val typeToCheck: BoundTypeReference,
    val reason: String,
    span: Span,
) : Diagnostic(
    Severity.WARNING,
    when (kind) {
        TypeCheckKind.INSTANCE_OF -> "This check is always false"
        TypeCheckKind.CAST -> "This cast can never succeed, it always throws"
        TypeCheckKind.SAFE_CAST -> "This cast can never succeed, it always evaluates to null"
    } + ": no value of type $typeOfValue is a $typeToCheck; $reason.",
    span,
)

enum class TypeCheckKind {
    /** `x is T` */
    INSTANCE_OF,
    /** `x as T` */
    CAST,
    /** `x as? T` */
    SAFE_CAST,
}

package compiler.diagnostic

import compiler.ast.type.AstTypeArgument
import compiler.lexer.Span

class ImmediateVariantTypeArgumentOnSupertypeDiagnostic(
    val erroneousArg: AstTypeArgument,
) : Diagnostic(
    Severity.ERROR,
    "Variance is not supported on arguments of immediate supertypes; a type is a subtype of an exact instance of its supertype. Remove the ${erroneousArg.variance.name.lowercase()}.",
    erroneousArg.span ?: Span.UNKNOWN
)

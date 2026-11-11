package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.lexer.Span

/**
 * @see ExclusiveTypeArgumentDiagnostic
 */
class ExclusiveTypeParameterBoundDiagnostic(
    val parameter: TypeParameter,
) : Diagnostic(
    Severity.ERROR,
    "The bound of type parameter ${parameter.name.value} cannot be exclusive, as type arguments cannot be exclusive.",
    parameter.bound?.span ?: parameter.name.span,
)

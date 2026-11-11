package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.lexer.Span

/**
 * @see OwnTypeArgumentDiagnostic
 */
class OwnTypeParameterBoundDiagnostic(
    val parameter: TypeParameter,
) : Diagnostic(
    Severity.ERROR,
    "The bound of type parameter ${parameter.name.value} cannot be of the mutability own, as type arguments cannot be.",
    parameter.bound?.span ?: parameter.name.span,
)

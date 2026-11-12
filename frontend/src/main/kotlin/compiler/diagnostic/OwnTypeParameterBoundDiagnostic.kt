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
    "Type arguments cannot be of the mutability own: it would allow generic code to duplicate the reference, which is not allowed for own values. Use mut, const or read here.",
    parameter.bound?.span ?: parameter.name.span,
)

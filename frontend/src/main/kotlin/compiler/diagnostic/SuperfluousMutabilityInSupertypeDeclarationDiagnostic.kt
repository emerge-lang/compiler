package compiler.diagnostic

import compiler.ast.type.TypeMutability
import compiler.lexer.Span

class SuperfluousMutabilityInSupertypeDeclarationDiagnostic(
    span: Span,
) : Diagnostic(
    Severity.INFO,
    "This mutability is superfluous, ${TypeMutability.top().keyword.text} is the default",
    span,
)
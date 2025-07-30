package compiler.diagnostic

import compiler.ast.type.TypeParameter

class UnsupportedDeclarationSiteVarianceDiagnostic(
    val parameter: TypeParameter,
) : Diagnostic(
    Severity.ERROR,
    "Declaration-site variance is not supported, yet",
    parameter.span,
)
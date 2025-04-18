package compiler.diagnostic

import compiler.ast.AstFunctionAttribute

class StaticFunctionDeclaredOverrideDiagnostic(
    val overrideAttribute: AstFunctionAttribute.Override,
) : Diagnostic(
    Severity.ERROR,
    "Static functions (no receiver declared) cannot override",
    overrideAttribute.sourceLocation,
)
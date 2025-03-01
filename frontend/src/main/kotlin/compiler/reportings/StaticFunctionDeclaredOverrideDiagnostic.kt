package compiler.reportings

import compiler.ast.AstFunctionAttribute

class StaticFunctionDeclaredOverrideDiagnostic(
    val overrideAttribute: AstFunctionAttribute.Override,
) : Diagnostic(
    Level.ERROR,
    "Static functions (no receiver declared) cannot override",
    overrideAttribute.sourceLocation,
)
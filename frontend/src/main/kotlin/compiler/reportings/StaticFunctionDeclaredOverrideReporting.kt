package compiler.reportings

import compiler.ast.AstFunctionAttribute

class StaticFunctionDeclaredOverrideReporting(
    val overrideAttribute: AstFunctionAttribute.Override,
) : Reporting(
    Level.ERROR,
    "Static functions (no receiver declared) cannot override",
    overrideAttribute.sourceLocation,
)
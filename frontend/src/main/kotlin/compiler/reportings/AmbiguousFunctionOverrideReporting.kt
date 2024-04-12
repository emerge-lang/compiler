package compiler.reportings

import compiler.ast.FunctionDeclaration

class AmbiguousFunctionOverrideReporting(
    val overridingFunction: FunctionDeclaration,
) : Reporting(
    Level.ERROR,
    "Function ${overridingFunction.name.value} overrides multiple functions. One of the parameters has a wider type than the method you are trying to override.",
    overridingFunction.declaredAt,
)
package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Keyword

class UndeclaredOverrideDiagnostic(
    val overridingFunction: FunctionDeclaration,
    val accidentalOverrideOnSupertype: BoundBaseType,
) : Diagnostic(
    Severity.ERROR,
    "Function ${overridingFunction.name.value} overrides a function of ${accidentalOverrideOnSupertype.simpleName}. It must be declared ${Keyword.OVERRIDE.name.lowercase()}.",
    overridingFunction.declaredAt,
)
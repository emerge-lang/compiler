package compiler.reportings

import compiler.ast.FunctionDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Keyword

class UndeclaredOverrideReporting(
    val overridingFunction: FunctionDeclaration,
    val accidentalOverrideOnSupertype: BoundBaseType,
) : Reporting(
    Level.ERROR,
    "Function ${overridingFunction.name.value} overrides a function of ${accidentalOverrideOnSupertype.simpleName}. It must be declared ${Keyword.OVERRIDE.name.lowercase()}.",
    overridingFunction.declaredAt,
)
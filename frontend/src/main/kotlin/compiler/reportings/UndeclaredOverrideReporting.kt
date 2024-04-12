package compiler.reportings

import compiler.ast.FunctionDeclaration
import compiler.binding.type.BaseType
import compiler.lexer.Keyword

class UndeclaredOverrideReporting(
    val overridingFunction: FunctionDeclaration,
    val accidentalOverrideOnSupertype: BaseType,
) : Reporting(
    Level.ERROR,
    "Function ${overridingFunction.name.value} overrides a function of ${accidentalOverrideOnSupertype.simpleName}. It must be declared ${Keyword.OVERRIDE.name.lowercase()}.",
    overridingFunction.declaredAt,
)
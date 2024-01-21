package compiler.reportings

import compiler.ast.expression.Expression
import compiler.ast.type.FunctionModifier
import compiler.binding.BoundFunction

data class FunctionMissingModifierReporting(
    val function: BoundFunction,
    val usageRequiringModifier: Expression<*>,
    val missingModifier: FunctionModifier
) : Reporting(
    Reporting.Level.ERROR,
    "Missing modifier \"${missingModifier.name.lowercase()}\" on function ${function.fullyQualifiedName}",
    usageRequiringModifier.sourceLocation,
) {
    init {
        check(missingModifier !in function.modifiers)
    }

    override fun toString() = super.toString() + "\ndeclared without this modifier here:\n${function.declaredAt}"
}
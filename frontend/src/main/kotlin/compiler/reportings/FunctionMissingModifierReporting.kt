package compiler.reportings

import compiler.ast.Expression
import compiler.binding.BoundFunction

data class FunctionMissingModifierReporting(
    val function: BoundFunction,
    val usageRequiringModifier: Expression,
    val missingAttribute: String,
) : Reporting(
    Reporting.Level.ERROR,
    "Missing modifier \"${missingAttribute::class.simpleName?.lowercase()}\" on function ${function.canonicalName}",
    usageRequiringModifier.span,
) {
    override fun toString() = super.toString() + "\ndeclared without this modifier here:\n${function.declaredAt}"
}
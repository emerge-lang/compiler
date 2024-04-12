package compiler.reportings

import compiler.ast.FunctionDeclaration

class IncompatibleReturnTypeOnOverrideReporting(
    val override: FunctionDeclaration,
    private val base: ValueNotAssignableReporting,
) : Reporting(
    Level.ERROR,
    "The return type of this override must be a subtype of the overridden functions return type: ${base.reason}",
    base.sourceLocation,
) {
    override fun toString() = "$levelAndMessage  overridden function returns: ${base.targetType}\n  override returns:            ${base.sourceType}\n\nin $sourceLocation"
}
package compiler.reportings

import compiler.ast.FunctionDeclaration
import compiler.binding.basetype.InheritedBoundMemberFunction

class IncompatibleReturnTypeOnOverrideDiagnostic(
    val override: FunctionDeclaration,
    val superFunction: InheritedBoundMemberFunction,
    private val base: ValueNotAssignableDiagnostic,
) : Diagnostic(
    Level.ERROR,
    "The return type of this override is not a subtype the overridden functions return type: ${base.reason}",
    base.span,
) {
    override fun toString() = "$levelAndMessage  overridden function: ${superFunction.canonicalName}\n  overridden function returns: ${base.targetType}\n  override returns:            ${base.sourceType}\n\nin $span"
}
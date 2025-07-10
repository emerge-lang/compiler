package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.binding.basetype.InheritedBoundMemberFunction

class IncompatibleReturnTypeOnOverrideDiagnostic(
    val override: FunctionDeclaration,
    val superFunction: InheritedBoundMemberFunction,
    private val base: ValueNotAssignableDiagnostic,
) : Diagnostic(
    Severity.ERROR,
    "The return type of this override is not a subtype the overridden functions return type: ${base.simplifiedMessage ?: base.reason}",
    base.span,
) {
    override fun toString() = "$levelAndMessage  overridden function:         ${superFunction.supertypeMemberFn.canonicalName}\n  overridden function returns: ${base.targetType}\n  override returns:            ${base.sourceType}\n\nin $span"
}
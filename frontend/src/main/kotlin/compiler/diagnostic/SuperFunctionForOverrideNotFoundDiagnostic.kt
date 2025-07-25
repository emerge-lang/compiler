package compiler.diagnostic

import compiler.ast.AstFunctionAttribute
import compiler.ast.FunctionDeclaration

class SuperFunctionForOverrideNotFoundDiagnostic(
    val overridingFunction: FunctionDeclaration,
    val baseTypeHasUnresolvedSuperTypes: Boolean,
) : Diagnostic(
    if (baseTypeHasUnresolvedSuperTypes) Severity.CONSECUTIVE else Severity.ERROR,
    "Function ${overridingFunction.name.value} doesn't override anything. The types of an overriding function must match exactly.",
    overridingFunction.attributes.first { it is AstFunctionAttribute.Override }.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is SuperFunctionForOverrideNotFoundDiagnostic) return false

        if (span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        return span.hashCode()
    }
}
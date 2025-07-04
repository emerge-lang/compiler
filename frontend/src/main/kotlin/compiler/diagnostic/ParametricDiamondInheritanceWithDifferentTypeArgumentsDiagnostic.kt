package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.binding.basetype.BoundBaseType
import compiler.binding.type.BoundTypeArgument
import compiler.lexer.Span

class ParametricDiamondInheritanceWithDifferentTypeArgumentsDiagnostic(
    val diamondRoot: BoundBaseType,
    val parameter: TypeParameter,
    inconsistentArguments: Set<BoundTypeArgument>,
    span: Span,
) : Diagnostic(
    if (inconsistentArguments.any { it.isPartiallyUnresolved }) Severity.CONSECUTIVE else Severity.ERROR,
    "Inconsistent arguments for parameter `${parameter.name.value}` of type `${diamondRoot.canonicalName}`: ${inconsistentArguments.joinToString(", ")}",
    span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ParametricDiamondInheritanceWithDifferentTypeArgumentsDiagnostic) return false

        if (other.span != this.span) return false
        if (other.diamondRoot !== this.diamondRoot) return false
        if (other.parameter.name.value !=  other.parameter.name.value) return false

        return true
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + span.hashCode()
        result = 31 * result + diamondRoot.hashCode()
        result = 31 * result + parameter.name.value.hashCode()

        return result
    }
}
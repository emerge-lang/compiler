package compiler.diagnostic

import compiler.ast.BaseTypeDeclaration
import compiler.binding.basetype.BoundSupertypeDeclaration
import compiler.lexer.Span

class CyclicInheritanceDiagnostic(
    onType: BaseTypeDeclaration,
    involvingSupertype: BoundSupertypeDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "Type ${onType.name.quote()} inheriting from ${involvingSupertype.resolvedReference!!.baseType.canonicalName.quote()} creates a cycle in the type hierarchy. That is not allowed.",
    involvingSupertype.astNode.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CyclicInheritanceDiagnostic) return false

        if (this.span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}
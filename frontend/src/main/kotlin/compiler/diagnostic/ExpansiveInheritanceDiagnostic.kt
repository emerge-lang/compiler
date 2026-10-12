package compiler.diagnostic

import compiler.ast.BaseTypeDeclaration
import compiler.binding.basetype.BoundSupertypeDeclaration
import compiler.lexer.Span

class ExpansiveInheritanceDiagnostic(
    onType: BaseTypeDeclaration,
    involvingSupertype: BoundSupertypeDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "Type ${onType.name.quote()} inheriting from ${involvingSupertype.resolvedReference!!.baseType.canonicalName.quote()} makes for expansive inheritance: a type parameter recurs, nested deeper, in its own supertypes. That is not allowed, as checking subtyping could go on forever.",
    involvingSupertype.astNode.span ?: Span.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ExpansiveInheritanceDiagnostic) return false

        if (this.span != other.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}

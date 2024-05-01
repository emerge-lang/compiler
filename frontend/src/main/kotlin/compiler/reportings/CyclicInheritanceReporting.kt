package compiler.reportings

import compiler.ast.BaseTypeDeclaration
import compiler.binding.basetype.BoundSupertypeDeclaration
import compiler.lexer.SourceLocation

class CyclicInheritanceReporting(
    onType: BaseTypeDeclaration,
    involvingSupertype: BoundSupertypeDeclaration,
) : Reporting(
    Level.ERROR,
    "Type ${onType.name.value} inheriting from ${involvingSupertype.resolvedReference!!.baseType.canonicalName} creates a cycle in the type hierarchy. That is not allowed.",
    involvingSupertype.astNode.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CyclicInheritanceReporting) return false

        if (this.sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + sourceLocation.hashCode()
        return result
    }
}
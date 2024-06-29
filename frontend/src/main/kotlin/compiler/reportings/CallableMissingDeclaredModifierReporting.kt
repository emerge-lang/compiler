package compiler.reportings

import compiler.ast.AstFunctionAttribute
import compiler.binding.BoundCallableRef

class CallableMissingDeclaredModifierReporting(
    callable: BoundCallableRef,
    val attribute: AstFunctionAttribute,
    reason: String,
) : Reporting(
    Level.ERROR,
    "$callable must have the ${attribute.attributeName.keyword.text} attribute: $reason",
    callable.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CallableMissingDeclaredModifierReporting) return false
        if (!super.equals(other)) return false

        if (span != other.span) return false
        if (attribute != other.attribute) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + attribute.hashCode()
        result = 31 * result + span.hashCode()
        return result
    }
}
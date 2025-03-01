package compiler.reportings

import compiler.ast.AstFunctionAttribute
import compiler.ast.FunctionDeclaration

class FunctionMissingDeclaredModifierDiagnostic(
    val fn: FunctionDeclaration,
    val attribute: AstFunctionAttribute,
    reason: String,
) : Diagnostic(
    Level.ERROR,
    "Function ${fn.name.value} must have the ${attribute.attributeName.keyword.text} attribute: $reason",
    fn.name.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is FunctionMissingDeclaredModifierDiagnostic) return false
        if (!super.equals(other)) return false

        if (fn != other.fn) return false
        if (attribute != other.attribute) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + fn.hashCode()
        result = 31 * result + attribute.hashCode()
        return result
    }
}
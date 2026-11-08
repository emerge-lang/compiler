package compiler.diagnostic

import compiler.ast.AstSemanticOperator
import compiler.ast.expression.UnaryExpression

/**
 * Reported on a prefix operator that binds weaker than the operator directly enclosing it, e.g. `a == not b`.
 */
class PrefixOperatorNeedsParenthesesDiagnostic(
    val expression: UnaryExpression,
    val enclosingOperator: AstSemanticOperator,
) : Diagnostic(
    Severity.ERROR,
    "Conflicting precedence between prefix operator ${expression.operator.name.lowercase()} and infix operator ${enclosingOperator.name.lowercase()}; parenthesize this expression for clarity.",
    expression.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is PrefixOperatorNeedsParenthesesDiagnostic) return false

        return expression == other.expression
    }

    override fun hashCode(): Int {
        return expression.hashCode()
    }
}

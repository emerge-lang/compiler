package compiler.diagnostic

import compiler.ast.expression.AstIndexedLengthExpression

class IndexedLengthOutsideIndexDiagnostic(
    val expression: AstIndexedLengthExpression,
) : Diagnostic(
    Severity.ERROR,
    "${'$'} is only allowed inside an index access, e.g. array[${'$'} - 1]",
    expression.span,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IndexedLengthOutsideIndexDiagnostic) return false

        return span == other.span
    }

    override fun hashCode(): Int {
        return span.hashCode()
    }
}

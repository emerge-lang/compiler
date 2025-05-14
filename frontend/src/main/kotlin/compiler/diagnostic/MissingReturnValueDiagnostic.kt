package compiler.diagnostic

import compiler.ast.ReturnExpression
import compiler.binding.type.BoundTypeReference

data class MissingReturnValueDiagnostic(
    val valueLessReturn: ReturnExpression,
    val expectedType: BoundTypeReference,
) : Diagnostic(
    Severity.ERROR,
    "Expecting a return value of type $expectedType",
    valueLessReturn.span,
) {
    override fun toString() = super.toString()
}
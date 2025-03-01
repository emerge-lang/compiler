package compiler.diagnostic

import compiler.ast.ReturnExpression
import compiler.binding.type.BoundTypeReference

data class MissingReturnValueDiagnostic(
    val valueLessReturn: ReturnExpression,
    val expectedType: BoundTypeReference,
) : Diagnostic(
    Level.ERROR,
    "Expecting a return value of type ${expectedType.simpleName}",
    valueLessReturn.span,
) {
    override fun toString() = super.toString()
}
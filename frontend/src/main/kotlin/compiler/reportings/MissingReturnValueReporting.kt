package compiler.reportings

import compiler.ast.ReturnExpression
import compiler.binding.type.BoundTypeReference

data class MissingReturnValueReporting(
    val valueLessReturn: ReturnExpression,
    val expectedType: BoundTypeReference,
) : Reporting(
    Level.ERROR,
    "Expecting a return value of type ${expectedType.simpleName}",
    valueLessReturn.span,
) {
    override fun toString() = super.toString()
}
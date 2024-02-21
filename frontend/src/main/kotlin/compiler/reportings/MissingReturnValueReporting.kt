package compiler.reportings

import compiler.ast.ReturnStatement
import compiler.binding.type.BoundTypeReference

data class MissingReturnValueReporting(
    val valueLessReturn: ReturnStatement,
    val expectedType: BoundTypeReference,
) : Reporting(
    Level.ERROR,
    "Expecting a return value of type ${expectedType.simpleName}",
    valueLessReturn.sourceLocation,
) {
    override fun toString() = super.toString()
}
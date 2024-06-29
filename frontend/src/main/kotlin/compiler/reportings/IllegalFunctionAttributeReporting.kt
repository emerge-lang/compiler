package compiler.reportings

import compiler.ast.AstFunctionAttribute

class IllegalFunctionAttributeReporting(
    val attribute: AstFunctionAttribute,
    reason: String,
) : Reporting(
    Level.ERROR,
    "attribute ${attribute.attributeName.keyword.name} is not allowed here: $reason",
    attribute.sourceLocation,
)
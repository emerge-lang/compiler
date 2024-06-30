package compiler.reportings

import compiler.ast.expression.AstTopLevelFunctionReference

class ReferencingUnknownTopLevelFunctionReporting(
    val reference: AstTopLevelFunctionReference,
) : Reporting(
    Level.ERROR,
    "Cannot resolve function ${reference.nameToken.value}",
    reference.span,
)
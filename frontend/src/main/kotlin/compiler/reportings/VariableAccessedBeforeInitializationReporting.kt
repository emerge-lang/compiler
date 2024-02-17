package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.ast.expression.IdentifierExpression

data class VariableAccessedBeforeInitializationReporting(
    val declaration: VariableDeclaration,
    val access: IdentifierExpression,
) : Reporting(
    Level.ERROR,
    "Variable ${declaration.name.value} has not been initialized yet. It must be initialized before use.",
    access.sourceLocation,
) {
    override fun toString() = super.toString()
}
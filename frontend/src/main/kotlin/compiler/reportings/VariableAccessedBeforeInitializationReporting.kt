package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.ast.expression.IdentifierExpression

data class VariableAccessedBeforeInitializationReporting(
    val declaration: VariableDeclaration,
    val access: IdentifierExpression,
    val maybeInitialized: Boolean,
) : Reporting(
    Level.ERROR,
    if (maybeInitialized) {
        "Variable ${declaration.name.value} may not have been initialized yet. Make sure to initialize it before use."
    } else {
        "Variable ${declaration.name.value} has not been initialized yet. It must be initialized before use."
    },
    access.sourceLocation,
) {
    override fun toString() = super.toString()
}
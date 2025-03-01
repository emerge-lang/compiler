package compiler.reportings

import compiler.ast.VariableDeclaration
import compiler.ast.expression.IdentifierExpression

data class VariableAccessedBeforeInitializationDiagnostic(
    val declaration: VariableDeclaration,
    val access: IdentifierExpression,
    val maybeInitialized: Boolean,
) : Diagnostic(
    Level.ERROR,
    if (maybeInitialized) {
        "Variable ${declaration.name.value} may not have been initialized yet. Make sure to initialize it before use."
    } else {
        "Variable ${declaration.name.value} has not been initialized yet. It must be initialized before use."
    },
    access.span,
) {
    override fun toString() = super.toString()
}
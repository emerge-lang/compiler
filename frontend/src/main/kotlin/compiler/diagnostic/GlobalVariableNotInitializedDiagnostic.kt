package compiler.diagnostic

import compiler.ast.VariableDeclaration

data class GlobalVariableNotInitializedDiagnostic(
    val declaration: VariableDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "Variable ${declaration.name.value} must be initialized at the declaration because it is a global.",
    declaration.span,
) {
    override fun toString() = super.toString()
}
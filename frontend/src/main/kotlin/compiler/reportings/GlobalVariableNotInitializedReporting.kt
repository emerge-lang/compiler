package compiler.reportings

import compiler.ast.VariableDeclaration

data class GlobalVariableNotInitializedReporting(
    val declaration: VariableDeclaration,
) : Reporting(
    Level.ERROR,
    "Variable ${declaration.name.value} must be initialized at the declaration because it is a global.",
    declaration.span,
) {
    override fun toString() = super.toString()
}
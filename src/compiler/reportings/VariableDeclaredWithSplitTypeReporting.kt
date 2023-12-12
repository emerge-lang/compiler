package compiler.reportings

import compiler.ast.VariableDeclaration

data class VariableDeclaredWithSplitTypeReporting(
    val declaration: VariableDeclaration,
) : Reporting(
    Reporting.Level.ERROR,
    "Variable declarations cannot have both an explicit mutability and an explicit type",
    declaration.sourceLocation,
) {
    override fun toString() = super.toString()
}
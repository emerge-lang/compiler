package compiler.reportings

import compiler.binding.BoundImportDeclaration

data class UnresolvableImportReporting(
    val import: BoundImportDeclaration,
) : Reporting(
    Level.ERROR,
    "Could not find a function, type or variable with the name ${import.simpleName} in package ${import.packageName}",
    import.declaration.identifiers.last().sourceLocation,
) {
    override fun toString() = super.toString()
}
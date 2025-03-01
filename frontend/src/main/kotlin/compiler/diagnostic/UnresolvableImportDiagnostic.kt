package compiler.diagnostic

import compiler.binding.BoundImportDeclaration

data class UnresolvableImportDiagnostic(
    val import: BoundImportDeclaration,
) : Diagnostic(
    Level.ERROR,
    "Could not find a function, type or variable with the name ${import.simpleName} in package ${import.packageName}",
    import.declaration.identifiers.last().span,
) {
    override fun toString() = super.toString()
}
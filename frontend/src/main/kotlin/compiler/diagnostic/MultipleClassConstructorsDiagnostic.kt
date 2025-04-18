package compiler.diagnostic

import compiler.ast.BaseTypeConstructorDeclaration

data class MultipleClassConstructorsDiagnostic(
    val additionalConstructors: Collection<BaseTypeConstructorDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    "Classes can have only one constructor. These must be removed",
    additionalConstructors.first().span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateSourceLocations(additionalConstructors.map { it.span })}"
}
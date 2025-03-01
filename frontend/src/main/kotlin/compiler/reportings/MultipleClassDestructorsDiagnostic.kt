package compiler.reportings

import compiler.ast.BaseTypeDestructorDeclaration

data class MultipleClassDestructorsDiagnostic(
    val additionalDestructors: Collection<BaseTypeDestructorDeclaration>,
) : Diagnostic(
    Level.ERROR,
    "Classes can have only one destructor. These must be removed",
    additionalDestructors.first().span,
) {
    override fun toString() = "$levelAndMessage\n${illustrateSourceLocations(additionalDestructors.map { it.span })}"
}
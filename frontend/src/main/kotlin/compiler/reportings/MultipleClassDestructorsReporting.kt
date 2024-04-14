package compiler.reportings

import compiler.ast.BaseTypeDestructorDeclaration

data class MultipleClassDestructorsReporting(
    val additionalDestructors: Collection<BaseTypeDestructorDeclaration>,
) : Reporting(
    Level.ERROR,
    "Classes can have only one destructor. These must be removed",
    additionalDestructors.first().sourceLocation,
) {
    override fun toString() = "$levelAndMessage\n${getIllustrationForHighlightedLines(additionalDestructors.map { it.sourceLocation })}"
}
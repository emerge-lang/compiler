package textutils.compiler.reportings

import compiler.ast.ClassDestructorDeclaration
import compiler.reportings.Reporting
import compiler.reportings.getIllustrationForHighlightedLines

data class MultipleClassDestructorsReporting(
    val additionalDestructors: Collection<ClassDestructorDeclaration>,
) : Reporting(
    Level.ERROR,
    "Classes can have only one destructor. These must be removed",
    additionalDestructors.first().declaredAt,
) {
    override fun toString() = "$levelAndMessage\n${getIllustrationForHighlightedLines(additionalDestructors.map { it.declaredAt })}"
}
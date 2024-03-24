package compiler.reportings

import compiler.ast.ClassConstructorDeclaration

data class MultipleClassConstructorsReporting(
    val additionalConstructors: Collection<ClassConstructorDeclaration>,
) : Reporting(
    Level.ERROR,
    "Classes can have only one constructor. These must be removed",
    additionalConstructors.first().declaredAt,
) {
    override fun toString() = "$levelAndMessage\n${getIllustrationForHighlightedLines(additionalConstructors.map { it.declaredAt })}"
}
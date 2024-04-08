package compiler.reportings

import compiler.ast.BaseTypeConstructorDeclaration

data class MultipleClassConstructorsReporting(
    val additionalConstructors: Collection<BaseTypeConstructorDeclaration>,
) : Reporting(
    Level.ERROR,
    "Classes can have only one constructor. These must be removed",
    additionalConstructors.first().declaredAt,
) {
    override fun toString() = "$levelAndMessage\n${getIllustrationForHighlightedLines(additionalConstructors.map { it.declaredAt })}"
}
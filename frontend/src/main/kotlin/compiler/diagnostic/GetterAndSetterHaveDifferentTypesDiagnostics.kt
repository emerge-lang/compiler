package compiler.diagnostic

import compiler.ast.FunctionDeclaration

class GetterAndSetterHaveDifferentTypesDiagnostics(
    val getter: FunctionDeclaration,
    val setter: FunctionDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "The getter and setter for virtual member variable `${getter.name.value}` disagree on the type of the variable.",
    getter.declaredAt,
) {
    override fun toString(): String {
        val setterParam = setter.parameters.parameters.drop(1).firstOrNull()
        val setterSpan = setterParam?.type?.span ?: setterParam?.span ?: setter.declaredAt
        return "$levelAndMessage\n${illustrateHints(listOf(
            SourceHint(getter.parsedReturnType?.span ?: getter.declaredAt, "the getter returns one type", relativeOrderMatters = false),
            SourceHint(setterSpan, "the setter takes another type", relativeOrderMatters = false),
        ))}"
    }
}